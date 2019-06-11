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
    ctx::SynthContext
    shape::MatrixShape
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
    maxsol::Number

    function Solutions(s::NLSolver, info::SynthInfo; maxsol=Inf)
        @assert maxsol >= 1
        new(s, NLSat.sat, Millisecond(0), info, maxsol)
    end
end

IteratorSize(::Type{Solutions}) = HasLength()
Base.length(s::Solutions) = s.maxsol

iterate(it::Solutions) = iterate(it, 0)

function iterate(s::Solutions, state)
    if isnothing(state) || state >= s.maxsol
        return nothing
    end
    s.status, s.elapsed, model = NLSat.solve(s.solver, timeout=s.info.timeout)
    if s.status == NLSat.sat
        A, B = s.info.ctx.init, s.info.ctx.body
        body = [get(model, Symbol(string(b)), b) for b in B]
        init = [get(model, Symbol(string(b)), b) for b in A]
        next_constraints!(s.solver, model)
        return SynthResult(Loop(init, body), s.elapsed, s.info), state+1
    end
    SynthResult(s.status, s.elapsed, s.info), nothing
end

function next_constraints!(s::NLSolver, m::Model)
    cs = [:($var != $val) for (var, val) in m]
    constraints!(s, [or(cs...)])
end

reason(s::Solutions) = SynthResult(s.status, s.elapsed, s.info)

# ------------------------------------------------------------------------------

struct SynthiePop{T<:NLSolver}
    body::Matrix{Basic}
    polys::Vector{Basic}
    vars::Vector{Basic}
    params::Vector{Basic}
    shape::MatrixShape
    maxsol::Number
    timeout::Int # seconds
    iterators::Vector{Any}

    function SynthiePop(polys::Vector{P}; 
                        solver::Type{S}=Yices, timeout::Int=10, maxsol::Int=1, 
                        shape::MatrixShape=full, vars::Vector{V}=Symbol[], 
                        params::Vector{V}=Symbol[]) where {S<:NLSolver, P<:Union{Basic,Expr}, V<:Union{Basic,Symbol}}

        polys  = map(Basic, polys)
        vars   = map(Basic, vars)
        params = map(Basic, params)
        fs = SymEngine.free_symbols(polys)
        xparams, xvars = filtervars(fs)
        if isempty(vars)
            vars = xvars
        else
            @assert issubset(xvars, vars) "Variables in polys ($(fs)) not a subset of given variables ($(vars))"
        end
        if isempty(params)
            params = xparams
        end

        dims = length(vars)
        body = dynamicsmatrix(dims, shape)
        if shape == uni
            part = partitions(dims, 1)
        else
            part = partitions(dims)
        end
        iters = [Iterators.product(part, permutations(vars))]
        new{S}(body, polys, vars, params, shape, maxsol, timeout, iters)
    end
end

# IteratorSize(::Type{SynthiePop}) = HasLength()
# Base.length(s::SynthiePop) = length(s.roots)

function iterate(S::SynthiePop)
    iter = first(S.iterators)
    next = iterate(iter)
    _iterate(S, next)
end

function _iterate(S::SynthiePop, state)
    state === nothing && return nothing
    sol = next_solution(S, first(state))
    push!(S.iterators, sol)
    result, next = iterate(sol)
    result, (next, last(state))
end

function iterate(S::SynthiePop, states)
    sstate, pstate = states
    next = iterate(last(S.iterators), sstate)
    if next === nothing
        iter1 = first(S.iterators)
        return _iterate(S, iterate(iter1, pstate))
    end
    first(next), (last(next), pstate)
end

function next_solution(s::SynthiePop{T}, next) where {T}
    roots, vars = next
    ctx = mkcontext(s.body, s.polys, vars, s.params, roots)
    varmap, cstr = constraints(ctx)
    cstropt = constraints_opt(ctx)
    solver = T()
    NLSat.variables!(solver, varmap)
    NLSat.constraints!(solver, cstr)
    NLSat.constraints!(solver, cstropt)
    info = SynthInfo(T, ctx, s.shape, s.timeout)
    Solutions(solver, info, maxsol=s.maxsol)
end

# ------------------------------------------------------------------------------

const Partitions = Union{Combinatorics.IntegerPartitions, Combinatorics.FixedPartitions}

struct Synthesizer{T<:NLSolver}
    body::Matrix{Basic}
    polys::Vector{Basic}
    roots::Partitions # multiplicities of roots
    vars::Vector{Basic}
    params::Vector{Basic}
    shape::MatrixShape
    timeout::Int # seconds

    function Synthesizer(::Type{T}, polys::Vector{Basic}, vars::Vector{Basic}, params::Vector{Basic}, shape::MatrixShape, timeout::Int) where {T<:NLSolver}
        dims = length(vars)
        body = dynamicsmatrix(dims, shape)
        if shape == uni
            part = partitions(dims, 1)
        else
            part = partitions(dims)
        end
        new{T}(body, polys, part, vars, params, shape, timeout)
    end
end

IteratorSize(::Type{Synthesizer}) = HasLength()
Base.length(s::Synthesizer) = length(s.roots)

iterate(s::Synthesizer) = next(s, iterate(s.roots))
iterate(s::Synthesizer, state) = next(s, iterate(s.roots, state))

function next(s::Synthesizer{T}, next) where {T}
    if next !== nothing
        (ms, state) = next
        ctx = mkcontext(s.body, s.polys, s.vars, s.params, ms)
        varmap, cstr = constraints(ctx)
        cstropt = constraints_opt(ctx)
        solver = T()
        NLSat.variables!(solver, varmap)
        NLSat.constraints!(solver, cstr)
        NLSat.constraints!(solver, cstropt)
        info = SynthInfo(T, ctx, s.shape, s.timeout)
        return Solutions(solver, info), state
    end
    return nothing
end

# ------------------------------------------------------------------------------

# function synth(args...; kwargs...) = SynthiePop(S, polys, vars, params, shape, timeout, maxsol)

# ------------------------------------------------------------------------------

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