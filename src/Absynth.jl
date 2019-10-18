module Absynth

using Logging
using Latexify
using MacroTools: walk, postwalk, @capture, @match, replace, striplines
using Combinatorics
using LinearAlgebra
using MultivariatePolynomials
using DynamicPolynomials
using Dates

const Var = AbstractVariable
const Poly = AbstractPolynomialLike

include("nlsat.jl")

using Absynth.NLSat

const Yices = YicesSolver
const Z3 = Z3Solver

export YicesSolver, Z3Solver, Yices, Z3

include("utils.jl")
include("types.jl")
include("cfinite.jl")
# include("constraints.jl")
# include("synthesizer.jl")
include("show.jl")
include("report.jl")
include("poly.jl")
include("macros.jl")
include("examples.jl")
include("frontend.jl")
include("iterators.jl")

export FullSymbolic, UpperTriangular, UnitUpperTriangular, Companion, UserSpecific
export Invariant, @invariant
export strategy_permutation, strategy_fixed
export models

# ------------------------------------------------------------------------------

_latex_logger = NullLogger()
latex_logger(l::AbstractLogger) = global _latex_logger = l
latex_logger() = _latex_logger

export latex_logger

# ------------------------------------------------------------------------------

end # module