module NLSat

export NLSolver, Z3Solver, YicesSolver
export NLStatus
export variables!, constraints!, solve

using PyCall
using DelimitedFiles
using Distributed
using MacroTools: walk, postwalk, @capture, @match, replace
using Dates

include("utils.jl")
include("clauseset.jl")

# Load Python libraries
const pyio = PyNULL()
const smtparser = PyNULL()
const z3 = PyNULL()
const yices = PyNULL()

z3_typemap = Dict{Type,Function}()
yices_typemap = Dict{Type,PyObject}()

function __init__()
    copy!(smtparser, pyimport("pysmt.smtlib.parser"))
    copy!(pyio, pyimport("io"))
    try
        copy!(z3, pyimport("z3"))
        push!(z3_typemap, Int             => z3.Int)
        push!(z3_typemap, Bool            => z3.Bool)
        push!(z3_typemap, AlgebraicNumber => z3.Real)
        push!(z3_typemap, Rational        => z3.Real)
        @info "Z3 available"
    catch
        @error "Could not load Z3"
    end

    try
        copy!(yices, pyimport("yices"))
        push!(yices_typemap, Int              => yices.Types.int_type())
        push!(yices_typemap, Bool             => yices.Types.bool_type())
        push!(yices_typemap, AlgebraicNumber  => yices.Types.real_type())
        push!(yices_typemap, Rational         => yices.Types.real_type())
        @info "Yices available"
    catch
        @error "Could not load Yices"
    end
end

# ------------------------------------------------------------------------------

abstract type AlgebraicNumber end
export AlgebraicNumber

# ------------------------------------------------------------------------------

@enum NLStatus sat unsat unknown timeout

abstract type NLSolver end

function variables!(s::NLSolver, d::Dict{Symbol,Type}) end
# function constraints!(s::NLSolver, c::Vector{Expr}) end
# function constraints!(s::NLSolver, c::ClauseSet) end
function solve(s::NLSolver; timeout::Int = -1) end

# ------------------------------------------------------------------------------

function openproc(parse::Function, cmd::Cmd; timeout=-1)
    start = time_ns()
    P = open(pipeline(cmd, stderr=devnull))
    if timeout < 0
        wait(P)
    else
        timedwait(()->!process_running(P), float(timeout))
        if process_running(P)
            @debug "Kill"
            kill(P)
            close(P.in)
            return NLSat.timeout, Second(timeout), nothing
        end
    end
    elapsed = Millisecond(round((time_ns()-start)/1e6))
    # Yices returns 0 and Z3 returns 1 on UNSAT
    if success(P) || P.exitcode == 1
        lines = readlines(P)
        status = popfirst!(lines)
        if status == "sat"
            d = parse(lines)
            return NLSat.sat, elapsed, d
        elseif status == "unsat"
            return NLSat.unsat, elapsed, nothing
        end

        @error("Unknown status: $status")
    end
    return NLSat.unknown, elapsed, nothing
end

# ------------------------------------------------------------------------------

function prefix(x::Expr)
    s = sprint(Meta.show_sexpr, x)
    s = Base.replace(s, ":call, " => "")
    s = Base.replace(s, ":" => "")
    s = Base.replace(s, "," => "")
    s = Base.replace(s, "(==)" => "=")
    s = Base.replace(s, "!=" => "distinct")
    s = Base.replace(s, "||" => "or")
    s = Base.replace(s, "//" => "/")
    s
end

prefix(c::Constraint{EQ}) = string("(= ", prefix(c.poly), " 0)")
prefix(c::Constraint{NEQ}) = string("(distinct ", prefix(c.poly), " 0)")

prefix(c::Clause) = length(c) == 1 ? prefix(first(c)) : string("(or ", join(map(prefix, c), " "), ")")

mutable struct YicesSolver <: NLSolver
    vars::Dict{Symbol,Type}
    cs::ClauseSet
    pyvars::Dict{Symbol, PyObject}
    cstr::Vector{PyObject}
    input::Vector{String}
    YicesSolver() = new(Dict(), ClauseSet(), Dict(), [], [])
end

function variables!(s::YicesSolver, d::Dict{Symbol,Type})
    for (v,t) in d
        pyvar = yices.Terms.new_uninterpreted_term(yices_typemap[t], string(v))
        push!(s.pyvars, v=>pyvar)
        push!(s.vars, v=>t)
    end
end

# function constraints!(s::YicesSolver, cstr::Vector{Expr})
#     for c in cstr
#         prefix_str = prefix(c)
#         term = yices.Terms.parse_term(prefix_str)
#         push!(s.cstr, term)
#         push!(s.input, yices.Terms.to_string(term, 200))
#     end
# end

constraints!(s::NLSolver, cs::ClauseSet) = s.cs &= cs

function solve(s::YicesSolver; timeout::Int = -1)
    cfg = yices.Config()
    cfg.default_config_for_logic("QF_NRA")
    ctx = yices.Context(cfg)

    for c in s.cs
        prefix_str = prefix(c)
        term = yices.Terms.parse_term(prefix_str)
        # push!(s.cstr, term)
        push!(s.input, yices.Terms.to_string(term, 200))
    end
    # ctx.assert_formulas(s.cstr)

    mktemp() do path, io
        write_yices(io, s)
        openproc(`yices --logic=QF_NRA $path`, timeout=timeout) do lines
            d = Dict{Symbol,Number}()
            for l in lines
                ll = l[4:end-1]
                (x,y) = split(ll, limit=2)
                sym = Symbol(x)
                val = parsenumber(y)
                push!(d, sym=>val)
            end
            d
        end
    end
end

function write_yices(io::IO, s::YicesSolver)
    for v in keys(s.vars)
        write(io, "(define $v::real)\n")
    end
    for x in s.input
        write(io, "(assert $x)\n")
    end
    write(io, "(check)\n")
    write(io, "(show-model)\n")
    close(io)
end

function parsenumber(s::AbstractString)
    T = Int
    ls = split(string(s), '/', keepempty=false)
    if length(ls) == 1
        return parse(T, ls[1])
    else
        @assert length(ls) == 2
        return parse(T, ls[1]) // parse(T, ls[2])
    end
end

# ------------------------------------------------------------------------------


struct Z3Solver <: NLSolver
    ptr::PyObject
    vars::Dict{Symbol, PyObject}
    cstr::Vector{PyObject}
    Z3Solver() = new(z3.SolverFor("QF_NRA"), Dict(), [])
end

function variables!(s::Z3Solver, d::Dict{Symbol,Type})
    for (var, type) in d
        push!(s.vars, var => z3_typemap[type](string(var)))
        if type == Rational
            p, q = gensym("p"), gensym("q")
            push!(s.vars, p => z3.Int(string(p)))
            push!(s.vars, q => z3.Int(string(q)))
            constraints!(s, [:($q > 0), :($p/$q == $(var))])
        end
    end
    s.vars
end

function _constraint!(s::Z3Solver, c::Union{PyObject,Bool})
    # TODO: do not accept boolean vars
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
        c = MacroTools.postwalk(x -> @capture(x, a_ || b_) ? :(z3.Or($a, $b)) : x, c)
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
    mktemp() do path, io
        write(io, s.ptr.to_smt2())
        write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
        close(io)

        openproc(`z3 $path`, timeout=timeout) do lines
            d = Dict{Symbol,Number}()
            parser = smtparser.SmtLibParser()
            @warn "Filtered root-obj. Needs fix!"
            filter!(x->!(occursin("root-obj", x)), lines)
            ls = parser.get_assignment_list(pyio.StringIO(join(lines)))
            for (var,val) in ls
                cval = val.constant_value()
                svar = Symbol(string(var))
                if val.is_int_constant()
                    push!(d, svar=>convert(Int, cval))
                elseif val.is_real_constant()
                    if typename(cval) == "mpq"
                        num = parse(Int, cval.numerator.digits()) 
                        den = parse(Int, cval.denominator.digits())
                        push!(d, svar=>Rational(num,den))
                    else
                        push!(d, svar=>convert(Float64, cval))
                    end
                elseif val.is_algebraic_constant()
                    # TODO
                    @warn "TODO: algebraic"
                else
                    @warn "Unknown data type of $((var,val))"
                end
            end
            return d
        end
    end
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

# mma_typemap = Dict{Type,Symbol}(
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
#         result = @FindInstance($(s.cstr), $([Element(v, mma_typemap[t]) for (v,t) in s.vars]))
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