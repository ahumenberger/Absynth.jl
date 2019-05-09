module NLSat

export NLSolver, Z3Solver
export variables!, constraints!, solve

using PyCall

# Load z3 Python library
const z3 = PyNULL()
const yices = PyNULL()

function __init__()
    copy!(z3, pyimport("z3"))
    copy!(yices, pyimport("yices"))
end

# ------------------------------------------------------------------------------

@enum NLStatus sat unsat unknown timeout

abstract type NLSolver end

function variables!(s::NLSolver, d::Dict{Symbol,Type}) end
function constraints!(s::NLSolver, c::Vector{Expr}) end
function solve(s::NLSolver; timeout::Int = -1) end

# ------------------------------------------------------------------------------

function prefix(x::Expr)
    s = sprint(Meta.show_sexpr, x)
    s = replace(s, ":call, " => "")
    s = replace(s, ":" => "")
    s = replace(s, "," => "")
    s = replace(s, "(==)" => "=")
    s = replace(s, "!=" => "distinct")
    s
end

yices_tmap = Dict{Type,PyObject}(
    Int             => yices.Types.int_type(),
    Bool            => yices.Types.bool_type(),
    AlgebraicNumber => yices.Types.real_type(),
    Rational        => yices.Types.real_type()
)

struct YicesSolver
    ptr::PyObject
    vars::Dict{Symbol, PyObject}
    cstr::Vector{PyObject}
end

function variables!(s::YicesSolver, d::Dict{Symbol,Type})
    for (s,t) in d
        pyvar = yices.Terms.new_uninterpreted_term(yices_tmap[t], string(s))
        push!(s.vars, s=>pyvar)
    end
end

function constraints!(s::YicesSolver, cstr::Vector{Expr})
    for c in cstr
        push!(s.cstr, yices.Terms.parse_term(prefix(c)))
    end
end

function solve(s::YicesSolver; timeout::Int = -1)
    cfg = yices.Config()
    cfg.default_config_for_logic('QF_NRA')
    ctx = yices.Context(cfg)
    ctx.assert_formulas(s.cstr)

    status = ctx.check_context()
    if status == yices.Status.SAT
        m = yices.Model.from_context(ctx, 1)
        mstr = m.to_string(80, 100, 0)
        @info "" mstr
    end
end

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
    Float32         => Z3Real,
    Rational        => Z3Real
)

struct Z3Solver <: NLSolver
    ptr::PyObject
    vars::Dict{Symbol, PyObject}
    cstr::Vector{PyObject}
    Z3Solver() = new(z3.SolverFor("QF_NRA"), Dict(), [])
end

function variables!(s::Z3Solver, d::Dict{Symbol,Type})
    for (var, type) in d
        push!(s.vars, var => typemap[type](string(var)))
        if type == Rational
            p, q = gensym("p"), gensym("q")
            push!(s.vars, p => Z3Int(string(p)))
            push!(s.vars, q => Z3Int(string(q)))
            constraints!(s, [:($q > 0), :($p/$q == $(var))])
        end
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
    # open("/Users/ahumenberger/Downloads/cstr.smt2", "w") do io
    #     write(io, s.ptr.to_smt2())
    # end
    result = s.ptr.check()
    if result == z3.sat
        return NLSat.sat
    elseif result == z3.unsat
        return NLSat.unsat
    elseif result == z3.unknown
        return NLSat.unknown
    end
    @info "Unknown result: $result"
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
            elseif vtype == "AlgebraicNumRef"
                val = parse(Float32, pyobj.as_decimal(10)[1:end-1])
            else
                @error "FIX NEEDED: unhandled type" vtype
            end
            push!(d, sym => val)
        end
        return res, d
    end
    res, nothing
end

typename(x::PyObject) = x.__class__.__name__

# ------------------------------------------------------------------------------

# try
#     using Mathematica
# catch
#     @info "MathematicaSolver not available. Everything else works."    
# end


# if @isdefined(Mathematica)

# export MathematicaSolver

# using Mathematica

# mmatypemap = Dict{Type,Symbol}(
#     Int => :Integers,
#     Rational => :Rationals,
#     AlgebraicNumber => :Algebraics
# )

# struct MathematicaSolver <: NLSolver
#     vars::Dict{Symbol,Type}
#     cstr::Vector{Expr}
#     MathematicaSolver() = new(Dict(), [])
# end

# function variables!(s::MathematicaSolver, d::Dict{Symbol,Type})
#     push!(s.vars, d...)
# end

# function constraints!(s::MathematicaSolver, cstr::Vector{Expr})
#     append!(s.cstr, cstr)
# end

# function solve(s::MathematicaSolver; timeout::Int=-1)
#     @debug "Constraints and variables" s.cstr s.vars
#     if timeout > 0
#         result = @TimeConstrained(FindInstance($(s.cstr), $(collect(keys(s.vars))), :AlgebraicNumbers), $(timeout), Timeout)
#     else
#         result = @FindInstance($(s.cstr), $([Element(v, mmatypemap[t]) for (v,t) in s.vars]))
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