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

function AlgebraicNumber(x::Expr, n::Int)
    @warn "Algebraic numbers not yet supported, got $((x, n)), returning $(NaN)"
    NaN
end

# ------------------------------------------------------------------------------

@enum NLStatus sat unsat unknown timeout

abstract type NLSolver end

function variables!(s::NLSolver, d::Dict{Symbol,Type}) end
function solve(s::NLSolver; timeout::Int = -1) end
constraints!(s::NLSolver, cs::ClauseSet) = s.cs &= cs

# ------------------------------------------------------------------------------

# include("mathematica.jl")
include("smt.jl")

end # module