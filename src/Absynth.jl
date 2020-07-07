module Absynth

using MacroTools: walk, postwalk, prewalk, @capture, @match, replace, striplines
using Combinatorics
using LinearAlgebra
using MultivariatePolynomials
using DynamicPolynomials
using Dates
using DataFrames: DataFrame, unstack, rename!
using ProgressMeter

const Var = AbstractVariable
const Poly = AbstractPolynomialLike
const SymOrNum = Union{Symbol,Number}

include("nlsat/NLSat.jl")

using Absynth.NLSat

export Z3Solver, SMTSolver, SMTSolverZ3, SMTSolverYices

include("utils.jl")
include("poly.jl")
include("invariant.jl")
include("cfinite.jl")
include("show.jl")
include("template.jl")
include("types.jl")
include("iterators.jl")

export FullSymbolic, UpperTriangular, UnitUpperTriangular, Companion, UserSpecific
export Invariant, @invariant
export solutions, models, synth
export RecSystem, loop
export RecTemplate
export AllPermutations, FixedPermutations
export AllPartitions, FixedPartitions
export Strategy
export @cstr

include("../benchmark/examples.jl")

end # module