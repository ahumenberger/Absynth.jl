using Z3
# : real_const, or, add, check

const Z3Expr = Z3.Expr

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

function _Z3Expr(ex::XExpr, vs::Dict{Symbol,Z3Expr})
    # @info "" vs
    t = symbol_walk(ex) do x
        get(vs, x, x)
    end
    # @info "" t
    # @info "" eval(t)
    eval(t)
end

function _Z3Expr(c::Constraint{EQ}, vs::Dict{Symbol,Z3Expr})
    _Z3Expr(c.poly, vs) == 0
end

function _Z3Expr(c::Constraint{NEQ}, vs::Dict{Symbol,Z3Expr})
    _Z3Expr(c.poly, vs) != 0
end

function _Z3Expr(c::Clause, vs::Dict{Symbol,Z3Expr})
    cs = [_Z3Expr(x, vs) for x in c]
    length(cs) > 1 && return or(cs...)
    cs[1]
end

function solve(s::CFiniteSolver; timeout::Int=-1)
    ctx = Context()
    z3vars = Dict{Symbol,Z3Expr}()
    for (k,v) in s.vars
        push!(z3vars, k=>real_const(ctx, string(k)))
    end
    # @info "" z3vars

    z3 = Solver(ctx, "QF_NRA")
    for cl in s.clauses
        # @info "" _Z3Expr(cl, z3vars)
        add(z3, _Z3Expr(cl, z3vars))
    end
    res = check(z3)
    if res == Z3.sat
        return sat, Dates.Second(5), parse_model(get_model(z3))
    elseif res == Z3.unsat
        return unsat
    elseif res == Z3.unknown
        return unknown
    end
end

function parse_model(m::Model)
    nlmodel = NLModel()
    for (k,v) in consts(m)
        sym = Symbol(string(k()))
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