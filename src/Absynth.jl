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

export SMTSolver
export Yices, Z3, CVC4
export exists, program_name

const Z3 = SMTSolver{:z3}
const CVC4 = SMTSolver{:cvc4}
const Yices = SMTSolver{(:yices,:-,:smt2)}

include("utils.jl")
include("poly.jl")
include("invariant.jl")
include("cfinite.jl")
include("show.jl")
include("examples.jl")
include("types.jl")
include("iterators.jl")

export FullSymbolic, UpperTriangular, UnitUpperTriangular, Companion, UserSpecific
export Invariant, @invariant
export strategy_all, strategy_permutations, strategy_partitions, strategy_fixed
export solutions, models
export loop

end # module