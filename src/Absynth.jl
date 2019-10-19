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

include("nlsat.jl")

using Absynth.NLSat

const Yices = YicesSolver
const Z3 = Z3Solver

export YicesSolver, Z3Solver, Yices, Z3

include("utils.jl")
include("poly.jl")
include("invariant.jl")
include("cfinite.jl")
include("show.jl")
include("examples.jl")
include("frontend.jl")
include("iterators.jl")

export FullSymbolic, UpperTriangular, UnitUpperTriangular, Companion, UserSpecific
export Invariant, @invariant
export strategy_permutation, strategy_fixed
export solutions, models

end # module