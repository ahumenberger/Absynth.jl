import Base: iterate, length, IteratorSize, HasLength, SizeUnknown

export Loop
export value

# ------------------------------------------------------------------------------

struct Loop
    init::Vector{Basic}
    body::Matrix{Basic}
end

value(l::Loop, k::Int) = l.body^k * l.init
value(l::Loop, r::UnitRange{Int}) = [value(l, k) for k in r]

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

struct Solutions
    solver::NLSolver
    info::SynthInfo
    maxsol::Number

    function Solutions(s::NLSolver, info::SynthInfo; maxsol = Inf)
        @assert maxsol >= 1
        new(s, info, maxsol)
    end
end

IteratorSize(::Type{Solutions}) = HasLength()
length(s::Solutions) = s.maxsol

iterate(it::Solutions) = iterate(it, 0)

function iterate(S::Solutions, state)
    (state === nothing || state >= S.maxsol) && return nothing
    status, elapsed, model = NLSat.solve(S.solver, timeout = S.info.timeout)
    if status == NLSat.sat
        A, B = S.info.ctx.init, S.info.ctx.body
        body = [get(model, Symbol(string(b)), b) for b in B]
        init = [get(model, Symbol(string(b)), b) for b in A]
        next_constraints!(S.solver, model)
        return SynthResult(Loop(init, body), elapsed, S.info), state + 1
    end
    SynthResult(status, elapsed, S.info), nothing
end

function next_constraints!(s::NLSolver, m::Model)
    cs = [:($var != $val) for (var, val) in m]
    constraints!(s, [or(cs...)])
end

# ------------------------------------------------------------------------------

struct Synthesizer{T <: NLSolver}
    body::Matrix{Basic}
    polys::Vector{Basic}
    vars::Vector{Basic}
    params::Vector{Basic}
    shape::MatrixShape
    maxsol::Number
    trivial::Bool
    timeout::Int # seconds
    iterators::Vector{Any}
end

function synth(polys; kwargs...)
    polys = map(Basic, polys)

    solver  = get(kwargs, :solver, Yices)
    timeout = get(kwargs, :timeout, 10)
    maxsol  = get(kwargs, :maxsol, 1)
    trivial = get(kwargs, :trivial, false)

    syms = SymEngine.free_symbols(polys)
    xparams, xvars = filtervars(syms)
    vars   = map(Basic, get(kwargs, :vars, xvars))
    params = map(Basic, get(kwargs, :params, xparams))
    @assert issubset(xvars, vars) "Variables in polys ($(xvars)) not a subset of given variables ($(vars))"

    shape = get(kwargs, :shape, full)
    dims = length(vars)
    body = dynamicsmatrix(dims, shape)
    part_iter = shape == uni ? partitions(dims, 1) : partitions(dims)
    
    perm = get(kwargs, :perm, shape in (uni, upper))
    perm_iter = perm ? permutations(vars) : [vars]
    iters = [Iterators.product(part_iter, perm_iter)]

    Synthesizer{solver}(body, polys, vars, params, shape, maxsol, trivial, timeout, iters)
end

# IteratorSize(::Type{Synthesizer}) = HasLength()
# Base.length(s::Synthesizer) = length(s.roots)

function iterate(S::Synthesizer)
    iter = first(S.iterators)
    next = iterate(iter)
    _iterate(S, next)
end

function _iterate(S::Synthesizer, state)
    state === nothing && return nothing
    sol = next_solution(S, first(state))
    push!(S.iterators, sol)
    result, next = iterate(sol)
    result, (next, last(state))
end

function iterate(S::Synthesizer, states)
    sstate, pstate = states
    next = iterate(last(S.iterators), sstate)
    if next === nothing
        iter1 = first(S.iterators)
        return _iterate(S, iterate(iter1, pstate))
    end
    first(next), (last(next), pstate)
end

function next_solution(S::Synthesizer{T}, next) where {T}
    roots, vars = next
    ctx = mkcontext(S.body, S.polys, vars, S.params, roots)
    varmap, cstr = constraints(ctx)
    solver = T()
    NLSat.variables!(solver, varmap)
    NLSat.constraints!(solver, cstr)
    if !S.trivial
        cstropt = constraints_opt(ctx)
        NLSat.constraints!(solver, cstropt)
    end
    info = SynthInfo(T, ctx, S.shape, S.timeout)
    Solutions(solver, info, maxsol = S.maxsol)
end