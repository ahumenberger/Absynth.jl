using Z3
# : real_const, or, add, check


const Z3Expr = Z3.Expr

include("maxsat.jl")

mutable struct CFiniteSolver <: NLSolver
    vars::Dict{Symbol,Type}
    clauses::ClauseSet
    function CFiniteSolver()
        new(Dict(), ClauseSet())
    end
end

function variables!(s::CFiniteSolver, d::Dict{Symbol,Type})
    push!(s.vars, d...)
end

function preprocess_clauseset(cs::ClauseSet)
    cl_cfin = []
    cl_norm = ClauseSet()
    for cl in cs
        # @info "" cl length(cl) typeof(cl) == CFiniteConstraint{EQ}
        if length(cl) == 1 && first(cl) isa CFiniteConstraint{EQ}
            push!(cl_cfin, first(cl))
        elseif length(cl) == 1 && cl isa CFiniteConstraint{NEQ}
            cl_norm &= expand(cl)
        else
            cl_norm &= cl
        end
    end
    cl_norm, cl_cfin
end

function find_partition(model::Model, ms)
    ps = Dict{Z3Expr,Vector{Int}}()
    for (i, m) in enumerate(ms)
        mval = Z3.eval(model, m, false)
        if haskey(ps, mval)
            push!(ps[mval], i)
        else
            push!(ps, mval=>Int[i])
        end
    end
    values(ps)
end

function check_partition(model::Model, us, ps)
    for subset in ps
        s = sum(us[i] for i in subset)
        if !is_true(Z3.eval(model, s == real_val(ctx(s), 0), false))
            return first(subset)
        end
    end
    nothing # all partitions are satisfied
end

function learn(s::Solver, ms, us, i)
    zero = real_val(ctx(s), 0)
    x = sum(ite(ms[i] == ms[j], us[j], zero) for j in 1:length(ms))
    add(s, x == 0)
end

function check_clauses(s::Solver, mss, uss)
    model = get_model(s)
    for (ms, us) in zip(mss, uss)
        ps = find_partition(model, ms)
        violated = check_partition(model, us, ps)
        if violated !== nothing
            # TODO: remove violated from us?
            learn(s, ms, us, violated)
            return false
        end
    end
    return true
end

function check_cfinite(s::Solver, vars, cs)
    uss = [[Z3Expr(ctx(s), vars, x) for x in c.us] for c in cs]
    mss = [[Z3Expr(ctx(s), vars, x) for x in c.ms] for c in cs]
    @info "" uss
    soft_clauses = Z3Expr[u == 0 for u in Iterators.flatten(uss)]
    # @info "Soft clauses" soft_clauses 
    max_it = length(soft_clauses)
    for _ in 1:max_it
        res, _ = maxsat(s, soft_clauses)
        res != NLSat.sat && return res # hard clauses not satisfiable or timeout
        sat = check_clauses(s, mss, uss)
        sat && return Z3.sat
    end
    NLSat.unsat
end

function solve(s::CFiniteSolver; timeout::Int=-1)
    ctx = main_ctx()
    # if timeout > 0
    # end
    z3vars = Dict{Symbol,Z3Expr}()
    for (k,v) in s.vars
        push!(z3vars, k=>real_const(ctx, string(k)))
    end
    
    cl_norm, cl_cfin = preprocess_clauseset(s.clauses)

    # @info "" z3vars

    z3 = Solver(ctx, "QF_NRA")
    set(ctx, "timeout", timeout*1000)
    for cl in cl_norm
        # @info "" cl
        # @info "nc" cl Z3Expr(ctx, z3vars, cl)
        add(z3, Z3Expr(ctx, z3vars, cl))
    end
    elapsed_sec = @elapsed res = check_cfinite(z3, z3vars, cl_cfin)

    # elapsed_sec = @elapsed res = check(z3)
    elapsed = Millisecond(round(elapsed_sec*1000))
    if res == Z3.sat
        return NLSat.sat, elapsed, parse_model(get_model(z3))
    elseif res == Z3.unsat
        return NLSat.unsat, elapsed, nothing
    elseif res == Z3.unknown
        reason = reason_unknown(z3)
        if reason == "timeout"
            return NLSat.timeout, elapsed, nothing
        end
        return NLSat.unknown, elapsed, nothing
    end
end

function parse_model(m::Model)
    nlmodel = NLModel()
    for (k,v) in consts(m)
        sym = Symbol(string(k))
        if is_int(v)
            push!(nlmodel, sym=>Int(v))
        elseif is_real(v)
            push!(nlmodel, sym=>try_int(Rational{Int}(v)))
        elseif is_algebraic(v)
            approx = get_decimal_string(v, 3)
            @warn "Algebraic numbers not yet supported, got $(v), returning approximation $(approx)"
            push!(nlmodel, sym=>approx)
        end
    end
    @info "" nlmodel
    nlmodel
end

# ------------------------------------------------------------------------------

function Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, ex::XExpr)
    t = postwalk(ex) do x
        if x isa Float64
            # if isinteger(x)
            #     convert(Int, x)
            # else
                y = rationalize(x)
                real_val(ctx, numerator(y), denominator(y))
            # end
        elseif issymbol(x)
            get(vs, x, x)
        else
            x
        end
    end
    eval(t)
end

Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{EQ}) = Z3Expr(ctx, vs, c.poly) == 0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{NEQ}) = Z3Expr(ctx, vs, c.poly) != 0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Clause) =
    length(c) > 1 ? or(Z3Expr(ctx, vs, x) for x in c) : Z3Expr(ctx, vs, first(c))