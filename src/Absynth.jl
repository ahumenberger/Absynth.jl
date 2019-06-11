module Absynth

using Logging
using Latexify
using MacroTools
using Combinatorics
using LinearAlgebra
using SymEngine
using SymPy
using Dates

include("nlsat.jl")

using Absynth.NLSat

const Yices = YicesSolver
const Z3 = Z3Solver

export YicesSolver, Z3Solver, Yices, Z3

include("constraints.jl")
include("synthesizer.jl")
include("show.jl")
include("report.jl")
include("utils.jl")

export synth, report, rerun

# ------------------------------------------------------------------------------

_latex_logger = NullLogger()
latex_logger(l::AbstractLogger) = global _latex_logger = l
latex_logger() = _latex_logger

export latex_logger

# ------------------------------------------------------------------------------

# atoms(f, ex) = MacroTools.postwalk(x -> x isa Symbol && Base.isidentifier(x) ? f(x) : x, ex)
# function free_symbols(ex::Expr)
#     ls = Symbol[]
#     atoms(x -> (push!(ls, x); x), ex)
#     Base.unique(ls)
# end

end # module