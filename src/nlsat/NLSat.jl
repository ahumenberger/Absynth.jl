module NLSat

export NLSolver, Z3Solver, YicesSolver, SMTSolver, CFiniteSolver
export NLStatus, NLModel
export add_vars!, add!, add_soft!, solve

using DataStructures
using DelimitedFiles
using Distributed
using MacroTools: walk, postwalk, @capture, @match, replace
using Dates

const NLModel = Dict{Symbol,Number}

# ------------------------------------------------------------------------------

abstract type AlgebraicNumber end
export AlgebraicNumber

function AlgebraicNumber(x::Expr, n::Int)
    @warn "Algebraic numbers not yet supported, got $((x, n)), returning $(NaN)"
    NaN
end

# ------------------------------------------------------------------------------

include("../utils.jl")
include("clauseset.jl")
include("smtlib.jl")
include("lisp.jl")

# ------------------------------------------------------------------------------

@enum NLStatus sat unsat unknown timeout

abstract type NLSolver end

function add_vars!(s::NLSolver, d::Dict{Symbol,Type}) end
function add!(s::NLSolver, cs::ClauseSet) end
function add_soft!(s::NLSolver, cs::ClauseSet) end
function solve(s::NLSolver; timeout::Int = -1) end

# ------------------------------------------------------------------------------

# include("mathematica.jl")
include("smtsolver.jl")
include("cfinitesolver.jl")

end # module