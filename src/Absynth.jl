module Absynth

using MacroTools
using SymEngine

include("nlsat.jl")

using Absynth.NLSat

const Yices = YicesSolver
const Z3 = Z3Solver

export YicesSolver, Z3Solver, Yices, Z3

include("alg.jl")

# ------------------------------------------------------------------------------

export Loop
export value, values

struct Loop
    vars::Vector{Basic}
    init::Vector{Basic}
    body::Matrix{Basic}
end

value(l::Loop, k::Int) = l.body^k * l.init
values(l::Loop, r::UnitRange{Int}) = [value(l, k) for k in r]

# ------------------------------------------------------------------------------

atoms(f, ex) = MacroTools.postwalk(x -> x isa Symbol && Base.isidentifier(x) ? f(x) : x, ex)
function free_symbols(ex::Expr)
    ls = Symbol[]
    atoms(x -> (push!(ls, x); x), ex)
    Base.unique(ls)
end

include("show.jl")

end # module
