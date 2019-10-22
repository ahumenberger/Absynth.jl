using MathLink

mma_typemap = Dict{Type,Symbol}(
    Int => :Integers,
    Rational => :Rationals,
    AlgebraicNumber => :Algebraics
)

mutable struct MathematicaSolver <: NLSolver
    vars::Dict{Symbol,Type}
    cs::ClauseSet
    MathematicaSolver() = new(Dict(), ClauseSet())
end

function variables!(s::MathematicaSolver, d::Dict{Symbol,Type})
    push!(s.vars, d...)
end

_tostring(cl::Clause) = join([string(convert(Expr, c)) for c in cl], " || ")
_tostring(cs::ClauseSet) = join([string("(", _tostring(cl), ")") for cl in cs], " && ")

function solve(s::MathematicaSolver; timeout::Int=-1)
    formula = MathLink.parseexpr(_tostring(s.cs))
    vars = MathLink.parseexpr(string("{", join(collect(keys(s.vars)), ", "), "}"))
    result = if timeout <= 0
        W"FindInstance"(formula, vars, W"Algebraics")
    else
        W"TimeConstrained"(W"FindInstance"(formula, vars, W"Algebraics"), timeout, W"Timeout")
    end
    start = time_ns()
    result = weval(result)
    elapsed = Millisecond(round((time_ns()-start)/1e6))
    res = _to_julia(result)
    if res == :Timeout
        return NLSat.timeout, Second(timeout), nothing
    elseif res == :Aborted
        @warn("Mathematica aborted")
        return NLSat.unknown, elapsed, nothing
    elseif isempty(res)
        return NLSat.unsat, elapsed, nothing
    end
    NLSat.sat, elapsed, Dict(first(res))
end

_to_julia(w::MathLink.WSymbol) = Symbol(w.name)
_to_julia(w::Number) = w
function _to_julia(w::MathLink.WExpr)
    if w.head == W"List"
        return [_to_julia(x) for x in w.args]
    elseif w.head == W"Rule"
        return _to_julia(w.args[1]) => _to_julia(w.args[2])
    elseif w.head == W"Rational"
        return _to_julia(w.args[1]) // _to_julia(w.args[2])
    elseif w.head == W"Complex"
        return _to_julia(w.args[1]) + _to_julia(w.args[2]) * im
    end
    w
end