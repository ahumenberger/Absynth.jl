module Absynth

using MacroTools
using SymEngine

include("nlsat.jl")
include("alg.jl")

using Absynth.NLSat

# ------------------------------------------------------------------------------

export Loop

struct Loop
    vars::Vector{Basic}
    init::Vector{Basic}
    body::Matrix{Basic}
end

# ------------------------------------------------------------------------------

atoms(f, ex) = MacroTools.postwalk(x -> x isa Symbol && Base.isidentifier(x) ? f(x) : x, ex)
function free_symbols(ex::Expr)
    ls = Symbol[]
    atoms(x -> (push!(ls, x); x), ex)
    Base.unique(ls)
end

include("show.jl")

end # module
