module NLSat

export NLSolver, Z3Solver, YicesSolver
export NLStatus, NLModel
export variables!, constraints!, solve

using PyCall
using DelimitedFiles
using Distributed
using MacroTools: walk, postwalk, @capture, @match, replace
using Dates

include("utils.jl")
include("clauseset.jl")

const NLModel = Dict{Symbol,Number}

# Load Python libraries
const pyio = PyNULL()
const smtparser = PyNULL()
const z3 = PyNULL()
const yices = PyNULL()

z3_typemap = Dict{Type,Function}()
yices_typemap = Dict{Type,PyObject}()

function _print_available(s::String, available::Bool)
    io = stdout
    status = available ? "available" : "not available"
    color = available ? :green : :red
    print(io, s)
    print(io, "\t")
    printstyled(io, status, color=color)
    print(io, "\n")
end

function __init__()
    copy!(smtparser, pyimport("pysmt.smtlib.parser"))
    copy!(pyio, pyimport("io"))
    try
        copy!(z3, pyimport("z3"))
        push!(z3_typemap, Int             => z3.Int)
        push!(z3_typemap, Bool            => z3.Bool)
        push!(z3_typemap, AlgebraicNumber => z3.Real)
        push!(z3_typemap, Rational        => z3.Real)
        _print_available("Z3", true)
    catch
        _print_available("Z3", false)
    end

    try
        copy!(yices, pyimport("yices"))
        push!(yices_typemap, Int              => yices.Types.int_type())
        push!(yices_typemap, Bool             => yices.Types.bool_type())
        push!(yices_typemap, AlgebraicNumber  => yices.Types.real_type())
        push!(yices_typemap, Rational         => yices.Types.real_type())
        _print_available("Yices", true)
    catch
        _print_available("Yices", false)
    end
end

# ------------------------------------------------------------------------------

abstract type AlgebraicNumber end
export AlgebraicNumber

# ------------------------------------------------------------------------------

@enum NLStatus sat unsat unknown timeout

abstract type NLSolver end

function variables!(s::NLSolver, d::Dict{Symbol,Type}) end
function solve(s::NLSolver; timeout::Int = -1) end
constraints!(s::NLSolver, cs::ClauseSet) = s.cs &= cs

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

prefix(x::Symbol) = string(x)
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

prefix(c::Clause) = length(c) == 1 ? prefix(first(c)) : string("(or ", join([prefix(x) for x in c], " "), ")")

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


mutable struct Z3Solver <: NLSolver
    ptr::PyObject
    vars::Dict{Symbol, PyObject}
    cs::ClauseSet
    cstr::Vector{PyObject}
    Z3Solver() = new(z3.SolverFor("QF_NRA"), Dict(), ClauseSet(), [])
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

function _set_constraints(s::Z3Solver)
    ls = Expr[]
    for (svar, z3var) in s.vars
        push!(ls, Expr(:(=), svar, z3var))
    end
    for cl in s.cs
        clause = if length(cl) == 1
            :($(convert(Expr, first(cl))))
        else
            :(z3.Or($([convert(Expr, c) for c in cl]...)))
        end
        expr = Expr(:block, ls..., clause)
        z3clause = eval(expr)
        s.ptr.add(z3clause)
        push!(s.cstr, z3clause)
    end
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
        _set_constraints(s)
        write(io, s.ptr.to_smt2())
        write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
        close(io)

        openproc(`z3 $path`, timeout=timeout) do lines
            d = Dict{Symbol,Number}()
            parser = smtparser.SmtLibParser()
            @warn "Filtering root-obj. Needs fix!"
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

# using MathLink

# mma_typemap = Dict{Type,Symbol}(
#     Int => :Integers,
#     Rational => :Rationals,
#     AlgebraicNumber => :Algebraics
# )

# mutable struct MathematicaSolver <: NLSolver
#     vars::Dict{Symbol,Type}
#     cs::ClauseSet
#     MathematicaSolver() = new(Dict(), ClauseSet())
# end

# function variables!(s::MathematicaSolver, d::Dict{Symbol,Type})
#     push!(s.vars, d...)
# end

# _tostring(cl::Clause) = join([string(convert(Expr, c)) for c in cl], " || ")
# _tostring(cs::ClauseSet) = join([string("(", _tostring(cl), ")") for cl in cs], " && ")

# function solve(s::MathematicaSolver; timeout::Int=-1)
#     formula = MathLink.parseexpr(_tostring(s.cs))
#     vars = MathLink.parseexpr(string("{", join(collect(keys(s.vars)), ", "), "}"))
#     result = if timeout <= 0
#         W"FindInstance"(formula, vars, W"Algebraics")
#     else
#         W"TimeConstrained"(W"FindInstance"(formula, vars, W"Algebraics"), timeout, W"Timeout")
#     end
#     start = time_ns()
#     result = weval(result)
#     elapsed = Millisecond(round((time_ns()-start)/1e6))
#     res = _to_julia(result)
#     if res == :Timeout
#         return NLSat.timeout, Second(timeout), nothing
#     elseif res == :Aborted
#         @warn("Mathematica aborted")
#         return NLSat.unknown, elapsed, nothing
#     elseif isempty(res)
#         return NLSat.unsat, elapsed, nothing
#     end
#     NLSat.sat, elapsed, Dict(first(res))
# end

# _to_julia(w::MathLink.WSymbol) = Symbol(w.name)
# _to_julia(w::Number) = w
# function _to_julia(w::MathLink.WExpr)
#     if w.head == W"List"
#         return [_to_julia(x) for x in w.args]
#     elseif w.head == W"Rule"
#         return _to_julia(w.args[1]) => _to_julia(w.args[2])
#     elseif w.head == W"Rational"
#         return _to_julia(w.args[1]) // _to_julia(w.args[2])
#     elseif w.head == W"Complex"
#         return _to_julia(w.args[1]) + _to_julia(w.args[2]) * im
#     end
#     w
# end

end # module