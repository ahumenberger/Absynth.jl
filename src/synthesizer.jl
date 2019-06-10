import Base: iterate, length, IteratorSize, HasLength, SizeUnknown

export Loop
export value, values

# ------------------------------------------------------------------------------

struct Loop
    init::Vector{Basic}
    body::Matrix{Basic}
end

value(l::Loop, k::Int) = l.body^k * l.init
values(l::Loop, r::UnitRange{Int}) = [value(l, k) for k in r]

# ------------------------------------------------------------------------------

struct SynthInfo
    solver::Type{<:NLSolver}
    vars::Vector{Basic}
    polys::Vector{Basic}
    roots::Vector{Int}
    shape::MatrixShape
    body::Matrix{Basic}
    timeout::Int
end

struct SynthResult
    result::Union{Loop,NLStatus}
    elapsed::TimePeriod
    info::SynthInfo
end

const Model = Dict{Symbol,Number}

# ------------------------------------------------------------------------------

mutable struct Solutions
    solver::NLSolver
    status::NLStatus
    elapsed::TimePeriod
    info::SynthInfo

    Solutions(s::NLSolver, info::SynthInfo) = new(s, NLSat.sat, Millisecond(0), info)
end

iterate(it::Solutions) = iterate(it, 0)

function iterate(it::Solutions, state)
    it.status, it.elapsed, model = NLSat.solve(it.solver, timeout=it.info.timeout)
    if it.status == NLSat.sat
        body = [isconstant(b) ? b : model[Symbol(string(b))] for b in it.info.body]
        init = [model[Symbol(string(b))] for b in initvec(size(it.info.body, 1))]
        next_constraints!(it.solver, model)
        return SynthResult(Loop(init, body), it.elapsed, it.info), state+1
    end
    return nothing
end

function next_constraints!(s::NLSolver, m::Model)
    cs = [:($var != $val) for (var, val) in m]
    constraints!(s, [or(cs...)])
end

reason(s::Solutions) = SynthResult(s.status, s.elapsed, s.info)

# ------------------------------------------------------------------------------

struct Synthesizer{T<:NLSolver}
    body::Matrix{Basic}
    polys::Vector{Basic}
    roots::Combinatorics.IntegerPartitions # multiplicities of roots
    vars::Vector{Basic}
    params::Vector{Basic}
    shape::MatrixShape
    timeout::Int # seconds

    function Synthesizer(::Type{T}, polys::Vector{Basic}, vars::Vector{Basic}, shape::MatrixShape, timeout::Int) where {T<:NLSolver}
        fs = SymEngine.free_symbols(polys)
        init, fs = filtervars(fs)
        @assert issubset(fs, vars) "Variables in polys ($(fs)) not a subset of given variables ($(vars))"

        dims = length(vars)
        body = dynamicsmatrix(dims, shape)
        new{T}(body, polys, partitions(dims), vars, init, shape, timeout)
    end
end

IteratorSize(::Type{Synthesizer}) = HasLength()
Base.length(s::Synthesizer) = length(s.roots)

iterate(s::Synthesizer) = next(s, iterate(s.roots))
iterate(s::Synthesizer, state) = next(s, iterate(s.roots, state))

function next(s::Synthesizer{T}, next) where {T}
    if next !== nothing
        (ms, state) = next
        varmap, cstr = constraints(s.body, s.polys, s.vars, s.params, ms)
        cstropt = constraints_opt(s.body)
        solver = T()
        NLSat.variables!(solver, varmap)
        NLSat.constraints!(solver, cstr)
        # NLSat.constraints!(solver, cstropt)
        info = SynthInfo(T, s.vars, s.polys, ms, s.shape, s.body, s.timeout)
        return Solutions(solver, info), state
    end
    return nothing
end

synth(x::Expr) = synth(Yices, [x])
synth(t::Type{T}, polys::Vector{Expr}) where {T<:NLSolver} =
    Synthesizer(t, polys, :F)

# ------------------------------------------------------------------------------

function synth(polys::Vector{P}; solver::Type{S}=Yices, timeout::Int=10, maxsol::Int=1, shape::MatrixShape=full, vars::Vector{V}=[]) where {S<:NLSolver, P<:Union{Basic,Expr}, V<:Union{Basic,Symbol}}
    polys = map(Basic, polys)
    vars = map(Basic, vars)
    fs = SymEngine.free_symbols(polys)
    _, xvars = filtervars(fs)
    if isempty(vars)
        vars = xvars
    end
    MultiSynthesizer(Synthesizer(S, polys, vars, shape, timeout), maxsol)
end

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