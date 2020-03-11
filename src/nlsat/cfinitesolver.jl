using Z3
# : real_const, or, add, check


const Z3Expr = Z3.Expr

include("maxsat.jl")

mutable struct CFiniteSolver <: NLSolver
    vars::Dict{Symbol,Type}
    hard_clauses::ClauseSet
    cfin_clauses::ClauseSet
    soft_clauses::ClauseSet
    function CFiniteSolver()
        new(Dict(), ClauseSet(), ClauseSet(), ClauseSet())
    end
end

function constraints!(s::CFiniteSolver, cs::ClauseSet)
    for c in cs
        if length(c) == 1 && first(c) isa CFiniteConstraint{EQ}
            s.cfin_clauses &= c
        else
            cl = Clause()
            for cstr in c
                cl |= expand(cstr)
            end
            s.hard_clauses &= cl
        end
    end
end
constraints_soft!(s::CFiniteSolver, cs::ClauseSet) = s.soft_clauses &= cs

function variables!(s::CFiniteSolver, d::Dict{Symbol,Type})
    push!(s.vars, d...)
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
    zero = real_val(ctx(model), 0)
    for subset in ps
        s = sum(us[i] for i in subset)
        if !is_true(Z3.eval(model, s == zero, false))
            return first(i for i in subset if is_true(Z3.eval(model, us[i] != zero, false)))
        end
    end
    nothing # all partitions are satisfied
end

function learn(s::Solver, ms, us, i)
    zero = real_val(ctx(s), 0)
    x = sum(ite(ms[i] == ms[j], us[j], zero) for j in 1:length(ms))
    @debug "Learn" x
    add(s, x == 0)
end

function check_clauses(s::Solver, model, mss, uss)
    for (ms, us) in zip(mss, uss)
        ps = find_partition(model, ms)
        violated = check_partition(model, us, ps)
        if violated !== nothing
            learn(s, ms, us, violated)
            return false
        end
    end
    return true
end

function check_cfinite(s::CFiniteSolver, z3::Solver, vars, soft_clauses)
    uss = [[Z3Expr(ctx(z3), vars, x) for x in c[1].us] for c in soft_clauses]
    mss = [[Z3Expr(ctx(z3), vars, x) for x in c[1].ms] for c in soft_clauses]

    soft_clauses = Z3Expr[u == 0 for u in Iterators.flatten(uss)]
    @debug "Soft clauses" soft_clauses

    max_it = length(soft_clauses)
    for _ in 1:max_it
        res, model = maxsat(z3, soft_clauses)
        res != Z3.sat && return res # hard clauses not satisfiable or timeout
        sat = check_clauses2(z3, model, mss, uss)
        sat && return Z3.sat
    end
    Z3.unsat
end

Tactic(s::String) = Z3.Tactic(main_ctx(), s)

function mk_solver()
    set_param("unsat_core", true)
    # set_param("verbose", 2)

    t = Tactic("simplify") & Tactic("propagate-values") & Tactic("solve-eqs") &
        Tactic("purify-arith") & Tactic("elim-term-ite") & Tactic("simplify") & Tactic("tseitin-cnf") &
        Tactic("nlsat")
    Z3.mk_solver(t)
end

function solve(s::CFiniteSolver; timeout::Int=-1)
    ctx = main_ctx()
    if timeout > 0
        set(ctx, "timeout", timeout*1000)
    end
    z3vars = Dict{Symbol,Z3Expr}()
    for (k,v) in s.vars
        push!(z3vars, k=>real_const(ctx, string(k)))
    end
    
    # z3 = Solver(ctx, "QF_NRA")
    z3 = mk_solver()
    for cl in s.hard_clauses
        add(z3, Z3Expr(ctx, z3vars, cl))
    end

    sclauses = ClauseSet()
    for cl in s.cfin_clauses
        if length(cl[1].us) == 1
            add(z3, Z3Expr(ctx, z3vars, cl[1].us[1]) == 0)
        else
            push!(sclauses, cl)
        end
    end

    elapsed_sec = @elapsed res = check_cfinite(s, z3, z3vars, sclauses)
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
        elseif x isa Int
            real_val(ctx, x)
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