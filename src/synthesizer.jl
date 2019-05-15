import Base: iterate, length, IteratorSize, HasLength

export Loop
export value, values

# ------------------------------------------------------------------------------

struct Loop
    vars::Vector{Basic}
    init::Vector{Basic}
    body::Matrix{Basic}
end

value(l::Loop, k::Int) = l.body^k * l.init
values(l::Loop, r::UnitRange{Int}) = [value(l, k) for k in r]

# ------------------------------------------------------------------------------

mutable struct Solutions
    solver::NLSolver
    status::NLStatus
    body::Matrix{Basic}
    vars::Vector{Basic}

    Solutions(s::NLSolver, b::Matrix{Basic}, vars::Vector{Basic}) = new(s, NLSat.sat, b, vars)
end

iterate(it::Solutions) = iterate(it, 0)

function iterate(it::Solutions, state)
    it.status, model = NLSat.solve(it.solver)
    if it.status == NLSat.sat
        body = [model[Symbol(string(b))] for b in it.body]
        init = [model[Symbol(string(b))] for b in initvec(size(it.body, 1))]
        return Loop(it.vars, init, body), state+1
    end
    return nothing
end

# ------------------------------------------------------------------------------

struct Synthesizer{T<:NLSolver}
    body::Matrix{Basic}
    polys::Vector{Basic}
    roots::Combinatorics.IntegerPartitions # multiplicities of roots
    vars::Vector{Basic}

    function Synthesizer(::Type{T}, polys::Vector{Expr}, shape::Symbol) where {T<:NLSolver}
        ps = map(Basic, polys)
        fs = SymEngine.free_symbols(ps)
        filter!(!isinitvar, fs)
    
        dims = length(fs)
        body = dynamicsmatrix(dims, shape)
        new{T}(body, ps, partitions(dims), fs)
    end
end

IteratorSize(::Type{Synthesizer}) = HasLength()
Base.length(s::Synthesizer) = length(s.roots)

iterate(s::Synthesizer) = next(s, iterate(s.roots))
iterate(s::Synthesizer, state) = next(s, iterate(s.roots, state))

function next(s::Synthesizer{T}, next) where {T}
    if next !== nothing
        (ms, state) = next
        varmap, cstr = constraints(s.body, s.polys, ms)
        solver = T()
        NLSat.variables!(solver, varmap)
        NLSat.constraints!(solver, cstr)
        return Solutions(solver, s.body, s.vars), state
    end
    return nothing
end

synth(x::Expr) = synth(Yices, [x])
synth(t::Type{T}, polys::Vector{Expr}) where {T<:NLSolver} =
    Synthesizer(t, polys, :F)
