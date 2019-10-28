module NLSat

export NLSolver, Z3Solver, YicesSolver, SMTSolver
export NLStatus, NLModel
export variables!, constraints!, solve

using DelimitedFiles
using Distributed
using MacroTools: walk, postwalk, @capture, @match, replace
using Dates

include("../utils.jl")
include("clauseset.jl")
include("smtlib.jl")
include("lisp.jl")

const NLModel = Dict{Symbol,Number}

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
        elseif status == "unknown"
            return NLSat.unknown, elapsed, nothing
        end

        error("Unknown status: $status")
    end
    return NLSat.unknown, elapsed, nothing
end

function parse_output_smt(s::Array{String})
    m = NLModel()
    sexpr = parse_sexpr(join(s))
    for x in sexpr.vec
        @assert length(x.vec) == 2
        sym = x.vec[1]
        val = try_int(eval(to_expr(x.vec[2])))
        push!(m, sym=>val)
    end
    m
end

function parse_output_yices(s::Array{String})
    m = NLModel()
    sexpr = parse_sexpr(string("(", join(s), ")"))
    for x in sexpr.vec
        @assert length(x.vec) == 3 && x.vec[1] == :(=) "$x"
        sym = x.vec[2]
        val = try_int(eval(to_expr(x.vec[3])))
        push!(m, sym=>val)
    end
    m
end

to_expr(x) = x isa SExpr ? Expr(:call, map(to_expr, x.vec)...) : x

try_int(x) = isinteger(x) ? convert(Int, x) : rationalize(x)

Base.rationalize(x::Rational) = x

# ------------------------------------------------------------------------------

# include("mathematica.jl")
include("smt.jl")

end # module