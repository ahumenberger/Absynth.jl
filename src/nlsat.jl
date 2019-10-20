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
const typing = PyNULL()
const pysmt = PyNULL()
const z3 = PyNULL()

z3_typemap = Dict{Type,Function}()
pysmt_typemap = Dict{Type,Expr}()
pysmt_opmap = Dict{Symbol,Expr}()
pysmt_relmap = Dict{ConstraintRel,Function}()

function _print_available(s::String, available::Bool, maxlen::Int)
    io = stdout
    status = available ? "found" : "not found"
    color = available ? :green : :red
    print(io, " ", s)
    print(io, fill(" ", maxlen - length(s))...)
    print(io, " => ")
    printstyled(io, status, color=color)
    print(io, "\n")
end

function __init__()
    copy!(smtparser, pyimport("pysmt.smtlib.parser"))
    copy!(pysmt, pyimport("pysmt.shortcuts"))
    copy!(typing, pyimport("pysmt.typing"))
    copy!(pyio, pyimport("io"))
    copy!(z3, pyimport("z3"))
    push!(z3_typemap, Int             => z3.Int)
    push!(z3_typemap, Bool            => z3.Bool)
    push!(z3_typemap, AlgebraicNumber => z3.Real)
    push!(z3_typemap, Rational        => z3.Real)


    push!(pysmt_typemap, Int             => :(typing.INT))
    push!(pysmt_typemap, Bool            => :(typing.BOOL))
    push!(pysmt_typemap, AlgebraicNumber => :(typing.REAL))
    push!(pysmt_typemap, Rational        => :(typing.REAL))

    push!(pysmt_opmap, :+ => :(pysmt.Plus))
    push!(pysmt_opmap, :- => :(pysmt.Minus))
    push!(pysmt_opmap, :* => :(pysmt.Times))

    push!(pysmt_relmap, EQ  => pysmt.Equals)
    push!(pysmt_relmap, NEQ => pysmt.NotEquals)
    push!(pysmt_relmap, LT  => pysmt.LT)
    push!(pysmt_relmap, LEQ => pysmt.LE)
    push!(pysmt_relmap, GT  => pysmt.GT)
    push!(pysmt_relmap, GEQ => pysmt.GE)

    solvers = (eval(k) for k in keys(smt_solvers))
    len = maximum(length(string(program_name(s))) for s in solvers)
    for s in solvers
        _print_available(program_name(s), isavailable(s), len)
    end

    !any(map(isavailable, solvers)) && @warn("No solver available.")
end

# ------------------------------------------------------------------------------

const smt_solvers = Dict(
    :Z3Solver    => "z3",
    :YicesSolver => "yices-smt2",
    :CVC4Solver  => "cvc4"
)

# ------------------------------------------------------------------------------

abstract type AlgebraicNumber end
export AlgebraicNumber

# ------------------------------------------------------------------------------

@enum NLStatus sat unsat unknown timeout

abstract type NLSolver end
abstract type SMTSolver <: NLSolver end

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
    if P.exitcode >= 0
        lines = readlines(P)
        status = popfirst!(lines)
        if status == "sat"
            d = parse(lines)
            return NLSat.sat, elapsed, d
        elseif status == "unsat"
            return NLSat.unsat, elapsed, nothing
        end

        error("Unknown status: $status")
    end
    return NLSat.unknown, elapsed, nothing
end

# ------------------------------------------------------------------------------

preprocess_smt(x::Expr) = postwalk(x) do y
    @match y begin
        b_^e_ => Expr(:call, :*, fill(b, e)...)
        -b_    => :((-1)*$b)
        _     => y
    end
end

tosmt(s::SMTSolver, x::Expr) = postwalk(preprocess_smt(x)) do sym
    if issymbol(sym)
        :(pysmt.Symbol($(string(sym)), $(pysmt_typemap[s.vars[sym]])))
    elseif sym isa Int
        :(pysmt.Real($sym))
    else
        get(pysmt_opmap, sym, sym)
    end
end |> eval

tosmt(s::SMTSolver, c::Constraint{R}) where {R} = pysmt_relmap[R](tosmt(s, c.poly), pysmt.Real(0))
tosmt(s::SMTSolver, c::Clause) = pysmt.Or([tosmt(s, x) for x in c])
tosmt(s::SMTSolver, c::ClauseSet) = pysmt.And([tosmt(s, x) for x in c])

# ------------------------------------------------------------------------------

for (name, program) in smt_solvers
    quote
        mutable struct $(name) <: SMTSolver
            vars::Dict{Symbol,Type}
            cs::ClauseSet
            
            function $(name)()
                @assert isavailable($(name))
                new(Dict(), ClauseSet())
            end
        end

        program_name(::Type{$(name)}) = $(program)
    end |> eval
end

program_name(::T) where {T<:SMTSolver} = program_name(T)
isavailable(s::Type{T}) where {T<:SMTSolver} = !isnothing(Sys.which(program_name(T)))

function variables!(s::SMTSolver, d::Dict{Symbol,Type})
    push!(s.vars, d...)
end

function write_smt(io::IO, s::SMTSolver)
    write(io, "(set-logic QF_NRA)\n")
    for (k,v) in s.vars
        t = eval(pysmt_typemap[v]).as_smtlib()
        write(io, "(declare-fun $k $t)\n")
    end
    write(io, "(assert ", pysmt.to_smtlib(tosmt(s, s.cs)), ")\n")
    write(io, "(check-sat)")
    write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
end

function solve(s::SMTSolver; timeout::Int=-1)
    mktemp() do path, io
        write_smt(io, s)
        close(io)

        openproc(`$(program_name(s)) $path`, timeout=timeout) do _lines
            d = Dict{Symbol,Number}()
            parser = smtparser.SmtLibParser()
            lines = filter!(x->!(occursin("root-obj", x)), _lines)
            _lines != lines && @warn "Sorry, I cannot parse algebraic numbers yet! Filtered root-obj."
            ls = parser.get_assignment_list(pyio.StringIO(join(lines)))
            for (var,val) in ls
                cval = val.constant_value()
                svar = Symbol(var.symbol_name())
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