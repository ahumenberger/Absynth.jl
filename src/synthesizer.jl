import Base: iterate, length, IteratorSize, HasLength, SizeUnknown

export Loop
export value, values

# ------------------------------------------------------------------------------

struct Loop
    vars::Vector{Basic}
    init::Vector{Basic}
    body::Matrix{Basic}

    polys::Vector{Basic}
    roots::Vector{Int}
end

value(l::Loop, k::Int) = l.body^k * l.init
values(l::Loop, r::UnitRange{Int}) = [value(l, k) for k in r]

# ------------------------------------------------------------------------------

mutable struct Solutions
    solver::NLSolver
    status::NLStatus
    timeout::Int # seconds
    body::Matrix{Basic}
    vars::Vector{Basic}
    polys::Vector{Basic}
    roots::Vector{Int} # multiplicities

    Solutions(s::NLSolver, timeout::Int, b::Matrix{Basic}, vars::Vector{Basic}, polys::Vector{Basic}, roots::Vector{Int}) =
        new(s, NLSat.sat, timeout, b, vars, polys, roots)
end

iterate(it::Solutions) = iterate(it, 0)

function iterate(it::Solutions, state)
    it.status, model = NLSat.solve(it.solver, timeout=it.timeout)
    if it.status == NLSat.sat
        body = [model[Symbol(string(b))] for b in it.body]
        init = [model[Symbol(string(b))] for b in initvec(size(it.body, 1))]
        return Loop(it.vars, init, body, it.polys, it.roots), state+1
    end
    return nothing
end

reason(s::Solutions) = s.status

# ------------------------------------------------------------------------------

struct Synthesizer{T<:NLSolver}
    body::Matrix{Basic}
    polys::Vector{Basic}
    roots::Combinatorics.IntegerPartitions # multiplicities of roots
    vars::Vector{Basic}
    timeout::Int # seconds

    function Synthesizer(::Type{T}, polys::Vector{Expr}, shape::Symbol) where {T<:NLSolver}
        ps = map(Basic, polys)
        fs = SymEngine.free_symbols(ps)
        filter!(!isinitvar, fs)
    
        dims = length(fs)
        body = dynamicsmatrix(dims, shape)
        new{T}(body, ps, partitions(dims), fs, 5)
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
        return Solutions(solver, s.timeout, s.body, s.vars, s.polys, ms), state
    end
    return nothing
end

synth(x::Expr) = synth(Yices, [x])
synth(t::Type{T}, polys::Vector{Expr}) where {T<:NLSolver} =
    Synthesizer(t, polys, :F)

# ------------------------------------------------------------------------------

synth(t::Type{T}, polys::Vector{Expr}, timeout::Int, maxsol::Int) where {T<:NLSolver} =
    MultiSynthesizer(Synthesizer(t, polys, :F), maxsol)

struct MultiSynthesizer{T<:NLSolver}
    synth::Synthesizer{T}
    maxsol::Int
end

IteratorSize(::Type{MultiSynthesizer}) = SizeUnknown()

iterate(ms::MultiSynthesizer) = first_sol(ms, iterate(ms.synth))

function iterate(ms::MultiSynthesizer, state)
    (synth_state, solutions, sol_state) = state
    if sol_state >= ms.maxsol
        next = iterate(ms.synth, synth_state)
        return first_sol(ms, next)
    else
        next_sol = iterate(solutions, sol_state)
        if next_sol !== nothing
            (loop, sol_state) = next_sol
            return loop, (synth_state, solutions, sol_state)
        else
            return reason(solutions), (synth_state, solutions, ms.maxsol)
        end
    end
end

function first_sol(ms::MultiSynthesizer, next)
    if next !== nothing
        (solutions, synth_state) = next
        next_sol = iterate(solutions)
        if next_sol !== nothing
            (loop, sol_state) = next_sol
            return loop, (synth_state, solutions, sol_state)
        else
            return reason(solutions), (synth_state, solutions, ms.maxsol)
        end
    end
end