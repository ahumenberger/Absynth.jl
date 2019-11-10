module Absynth

using MacroTools: walk, postwalk, @capture, @match, replace, striplines
using Combinatorics
using LinearAlgebra
using MultivariatePolynomials
using DynamicPolynomials
using Dates
using DataFrames: DataFrame, unstack, rename!
using ProgressMeter

const Var = AbstractVariable
const Poly = AbstractPolynomialLike

include("nlsat/NLSat.jl")

using Absynth.NLSat

const Yices = YicesSolver
# const Z3 = Z3Solver

export YicesSolver, Z3Solver, Yices, SMTSolver

include("utils.jl")
include("poly.jl")
include("invariant.jl")
include("cfinite.jl")
include("show.jl")
include("types.jl")
include("iterators.jl")

export FullSymbolic, UpperTriangular, UnitUpperTriangular, Companion, UserSpecific
export Invariant, @invariant
export strategy_all, strategy_permutations, strategy_partitions, strategy_fixed, strategy_mixed
export solutions, models, synth
export RecSystem, loop

include("../benchmark/examples.jl")

end # module