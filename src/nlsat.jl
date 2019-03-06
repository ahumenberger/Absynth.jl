module NLSat

export NLSolver, Z3Solver
export variables!, constraints!, solve

using PyCall

# Load z3 Python library
const z3 = PyNULL()

function __init__()
    copy!(z3, pyimport("z3"))
end

# ------------------------------------------------------------------------------

@enum NLStatus sat unsat unknown

abstract type NLSolver end

function variables!(s::NLSolver, d::Pair{Symbol,Type}...) end
function constraints!(s::NLSolver, c::Expr...) end
function solve(s::NLSolver; timeout::Int = -1) end

# ------------------------------------------------------------------------------

Z3Real(name::String) = z3.Real(name)
Z3Int(name::String) = z3.Int(name)
Z3Bool(name::String) = z3.Bool(name)

struct Z3Solver <: NLSolver
    ptr::PyObject
    vars::Dict{Symbol, PyObject}
    cstr::Vector{PyObject}
    Z3Solver() = new(z3.Solver(), Dict(), [])
end

function variables!(s::Z3Solver, d::Pair{Symbol,Type}...)
    for (k, v) in d
        if v != Int
            # @warn "Type $v not supported, using $(Int64): $k"
            v = Int
        end
        push!(s.vars, k => Z3Int(string(k)))
    end
    s.vars
    # Dict(zip(keys(d), s.vars))
end

function _constraint!(s::Z3Solver, c::PyObject)
    s.ptr.add(c)
    push!(s.cstr, c)
    c
end

function constraints!(s::Z3Solver, cstr::Expr...)
    for c in cstr
        ls = Expr[]
        for (svar, z3var) in s.vars
            push!(ls, Expr(:(=), svar, z3var))
        end
        expr = Expr(:block, ls..., c)
        z3cstr = eval(expr)
        _constraint!(s, z3cstr)
    end
    s.cstr[end-length(cstr)+1:end]
end

function _check(s::Z3Solver)
    result = s.ptr.check()
    if result == z3.sat
        return sat
    elseif result == z3.unsat
        return unsat
    end
    @info "Unknown result: $result"
    return unknown
end

function solve(s::Z3Solver; timeout::Int = -1)
    @warn "$(typeof(s)) only supports Integer solutions for now."
    if timeout > 0
        z3.set(timeout=timeout)
    end
    res = _check(s)
    if res == sat
        m = s.ptr.model()
        d = Dict{Symbol,Int}()
        for v in m
            push!(d, Symbol(string(v.name())) => convert(Int, m.__getitem__(v).as_long()))
        end
        return res, d
    end
    res, nothing
end

# ------------------------------------------------------------------------------

try
    using Mathematica
catch
    @info "MathematicaSolver not available. Everything else works."    
end


if @isdefined(Mathematica)

export MathematicaSolver

struct MathematicaSolver <: NLSolver
    vars::Dict{Symbol,Type}
    cstr::Vector{Expr}
    MathematicaSolver() = new(Dict(), [])
end

function variables!(s::MathematicaSolver, d::Pair{Symbol,Type}...)
    push!(s.vars, d...)
end

function constraints!(s::MathematicaSolver, cstr::Expr...)
    push!(s.cstr, cstr...)
end

function solve(s::MathematicaSolver; timeout::Int = -1)
    @debug "Constraints and variables" s.cstr s.vars
    result = FindInstance(s.cstr, collect(keys(s.vars)), :Rationals)
    @debug "Result of Mathematica" result
    if isempty(result)
        return unsat, nothing
    end
    return sat, Dict(result[1]...)
end

end #if

end # module