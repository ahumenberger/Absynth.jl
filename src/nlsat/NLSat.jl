module NLSat

export NLSolver, Z3Solver, YicesSolver, SMTSolver
export NLStatus, NLModel
export variables!, constraints!, solve

using PyCall
using DelimitedFiles
using Distributed
using MacroTools: walk, postwalk, @capture, @match, replace
using Dates

include("../utils.jl")
include("clauseset.jl")

const NLModel = Dict{Symbol,Number}

typename(x::PyObject) = x.__class__.__name__

# Load Python libraries
const z3        = PyNULL()
const yices     = PyNULL()
const pyio      = PyNULL()
const smtparser = PyNULL()
const typing    = PyNULL()
const pysmt     = PyNULL()

pysmt_typemap = Dict{Type,Expr}()
pysmt_opmap   = Dict{Symbol,Expr}()
pysmt_relmap  = Dict{ConstraintRel,Function}()

z3_typemap    = Dict{Type,Function}()
yices_typemap = Dict{Type,PyObject}()

function __init__()
    copy!(smtparser, pyimport("pysmt.smtlib.parser"))
    copy!(pysmt,     pyimport("pysmt.shortcuts"))
    copy!(typing,    pyimport("pysmt.typing"))
    copy!(pyio,      pyimport("io"))
    copy!(z3,        pyimport("z3"))
    copy!(yices,     pyimport("yices"))

    init_z3()
    init_yices()
    init_pysmt()
end

function init_z3()
    push!(z3_typemap, Int             => z3.Int)
    push!(z3_typemap, Bool            => z3.Bool)
    push!(z3_typemap, AlgebraicNumber => z3.Real)
    push!(z3_typemap, Rational        => z3.Real)
end

function init_yices()
    push!(yices_typemap, Int              => yices.Types.int_type())
    push!(yices_typemap, Bool             => yices.Types.bool_type())
    push!(yices_typemap, AlgebraicNumber  => yices.Types.real_type())
    push!(yices_typemap, Rational         => yices.Types.real_type())
end

function init_pysmt()
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

function parse_smtoutput(_lines::Vector{String})
    d = NLModel()
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
    @info "" d
    return d
end

# ------------------------------------------------------------------------------

# include("mathematica.jl")
include("smt.jl")
include("z3.jl")
include("yices.jl")

end # module