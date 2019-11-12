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

function _Z3Expr(ctx::Context, ex::XExpr, vs::Dict{Symbol,Z3Expr})
    # @info "" vs
    t = postwalk(ex) do x
        if x isa Float64
            if isinteger(x)
                convert(Int, x)
            else
                y = rationalize(x)
                real_val(ctx, numerator(y), denominator(y))
            end
        elseif issymbol(x)
            # @info "" x
            get(vs, x, x)
        else
            x
        end
    end
    # @info "" t
    # @info "" eval(t)
    eval(t)
end

function _Z3Expr(ctx::Context, c::Constraint{EQ}, vs::Dict{Symbol,Z3Expr})
    _Z3Expr(ctx, c.poly, vs) == 0
end

function _Z3Expr(ctx::Context, c::Constraint{NEQ}, vs::Dict{Symbol,Z3Expr})
    _Z3Expr(ctx, c.poly, vs) != 0
end

function _Z3Expr(ctx::Context, c::Clause, vs::Dict{Symbol,Z3Expr})
    cs = [_Z3Expr(ctx, x, vs) for x in c]
    length(cs) > 1 && return or(cs...)
    cs[1]
end

function preprocess_clauseset(cs::ClauseSet)
    cl_cfin = ClauseSet()
    cl_norm = ClauseSet()
    for cl in cs
        if length(cl) == 1 && cl isa CFiniteConstraint{EQ}
            cl_cfin &= cl
        elseif length(cl) == 1 && cl isa CFiniteConstraint{NEQ}
            cl_norm &= expand(cl)
        else
            cl_norm &= cl
        end
    end
    cl_norm, cl_cfin
end

function solve(s::CFiniteSolver; timeout::Int=-1)
    ctx = Context()
    if timeout > 0
        set(ctx, "timeout", timeout*1000)
    end
    z3vars = Dict{Symbol,Z3Expr}()
    for (k,v) in s.vars
        push!(z3vars, k=>real_const(ctx, string(k)))
    end
    
    cl_norm, cl_cfin = preprocess_clauseset(s.clauses)

    # @info "" z3vars

    z3 = Solver(ctx, "QF_NRA")
    for cl in s.clauses
        # @info "" cl
        # @info "" cl _Z3Expr(ctx, cl, z3vars)
        add(z3, _Z3Expr(ctx, cl, z3vars))
    end
    elapsed_sec = @elapsed res = check(z3)
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