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

@enum NLStatus sat unsat unknown timeout

abstract type NLSolver end

function variables!(s::NLSolver, d::Pair{Symbol,Type}...) end
function constraints!(s::NLSolver, c::Expr...) end
function solve(s::NLSolver; timeout::Int = -1) end

# ------------------------------------------------------------------------------

Z3Real(name::String) = z3.Real(name)
Z3Int(name::String) = z3.Int(name)
Z3Bool(name::String) = z3.Bool(name)

abstract type AlgebraicNumber end
export AlgebraicNumber

typemap = Dict{Type,Function}(
    Int             => Z3Int,
    Bool            => Z3Bool,
    AlgebraicNumber => Z3Real,
    Float32         => Z3Real
)

struct Z3Solver <: NLSolver
    ptr::PyObject
    vars::Dict{Symbol, PyObject}
    cstr::Vector{PyObject}
    Z3Solver() = new(z3.Solver(), Dict(), [])
end

function variables!(s::Z3Solver, d::Dict{Symbol,Type})
    for (var, type) in d
        push!(s.vars, var => typemap[type](string(var)))
    end
    s.vars
end

function _constraint!(s::Z3Solver, c::PyObject)
    s.ptr.add(c)
    push!(s.cstr, c)
    c
end

function constraints!(s::Z3Solver, cstr::Vector{Expr})
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
        return NLSat.sat
    elseif result == z3.unsat
        return NLSat.unsat
    end
    @debug "Unknown result: $result"
    # Z3 returns 'unknown' on timeout
    return NLSat.timeout
end

function solve(s::Z3Solver; timeout::Int=-1)
    @debug "$(typeof(s)) only supports Integer solutions for now."
    if timeout > 0
        # Z3 expects milliseconds
        s.ptr.set(timeout=timeout*1000)
    end
    res = _check(s)
    if res == sat
        m = s.ptr.model()
        d = Dict{Symbol,Number}()
        for v in m
            sym = Symbol(string(v.name()))
            pyobj = m.__getitem__(v)
            vtype = typename(pyobj)
            if vtype == "IntNumRef"
                val = convert(Int, pyobj.as_long())
            elseif vtype == "RatNumRef"
                num = pyobj.numerator_as_long()
                den = pyobj.denominator_as_long()
                val = Rational(num, den)
            else
                @error "FIX NEEDED: unhandled type"
            end
            @info sym val
            push!(d, sym => val)
        end
        return res, d
    end
    res, nothing
end

typename(x::PyObject) = x.__class__.__name__
get(m::Py)

# ------------------------------------------------------------------------------

# try
#     using Mathematica
# catch
#     @info "MathematicaSolver not available. Everything else works."    
# end


# if @isdefined(Mathematica)

# export MathematicaSolver

# struct MathematicaSolver <: NLSolver
#     vars::Dict{Symbol,Type}
#     cstr::Vector{Expr}
#     MathematicaSolver() = new(Dict(), [])
# end

# function variables!(s::MathematicaSolver, d::Pair{Symbol,Type}...)
#     push!(s.vars, d...)
# end

# function constraints!(s::MathematicaSolver, cstr::Expr...)
#     push!(s.cstr, cstr...)
# end

# function solve(s::MathematicaSolver; timeout::Int=-1)
#     @debug "Constraints and variables" s.cstr s.vars
#     if timeout > 0
#         result = @TimeConstrained(FindInstance($(s.cstr), $(collect(keys(s.vars))), :Integers), $(timeout), Timeout)
#     else
#         result = FindInstance(s.cstr, collect(keys(s.vars)), :Integers)
#     end
#     @debug "Result of Mathematica" result
#     if result == :Timeout
#         return NLSat.timeout, nothing
#     elseif isempty(result)
#         return NLSat.unsat, nothing
#     end
#     return NLSat.sat, Dict(result[1]...)
# end

# end #if

end # module