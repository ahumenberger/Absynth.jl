import Base: iterate, length, IteratorSize, HasLength, SizeUnknown

export Loop
export value

# ------------------------------------------------------------------------------

struct Loop
    vars::Vector{<:Var}
    params::Vector{<:Poly}
    init::Matrix{<:Number}
    body::Matrix{<:Number}
end

value(l::Loop, k::Int) = l.body^k * l.init
value(l::Loop, r::UnitRange{Int}) = [value(l, k) for k in r]

function sequentialize(M::Matrix, v::Vector)
    M, v
end

function code(l::Loop)
    body, vars = sequentialize(l.body, l.vars)
    lhss = (Meta.parse ∘ string).(body * vars)
    init = [:($rhs = $lhs) for (rhs,lhs) in zip(l.vars, l.init*l.params)]
    assign = [:($rhs = $lhs) for (rhs,lhs) in zip(vars, lhss)]
    MacroTools.striplines(quote
        $(init...)
        while true
            $(assign...)
        end
    end)
end

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

issat(s::SynthResult) = s.result isa Loop

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
        ctx = S.info.ctx
        A, B = ctx.init, ctx.body
        params = ctx.params
        body = Number[get(model, Symbol(string(b)), b) for b in B]
        init = Number[get(model, Symbol(string(b)), b) for b in A]
        next_constraints!(S.solver, model)
        return SynthResult(Loop(ctx.vars, params, init, body), elapsed, S.info), state + 1
    end
    SynthResult(status, elapsed, S.info), nothing
end

function next_constraints!(s::NLSolver, m::Model)
    cs = [:($var != $val) for (var, val) in m]
    constraints!(s, [or(cs...)])
end

# ------------------------------------------------------------------------------

struct VarPerm
    vars::Vector{<:Var}
    one::Var # constant 1

    VarPerm(vars::Vector{<:Var}, one::Var=mkvar(:cc)) = new(vars, one)
end

function iterate(V::VarPerm)
    P = permutations(V.vars)
    _iterate(V, P, iterate(P))
end

function _iterate(V::VarPerm, P, next)
    next === nothing && return nothing
    perm, state = next
    [perm; V.one], (P, state)
end

function iterate(V::VarPerm, next)
    next === nothing && return nothing
    P, state = next
    _iterate(V, P, iterate(P, state))
end

# ------------------------------------------------------------------------------

struct Synthesizer{T <: NLSolver}
    body::Matrix{<:Poly}
    polys::Vector{<:Poly}
    vars::Vector{<:Var}
    params::Vector{<:Var}
    shape::MatrixShape
    maxsol::Number
    trivial::Bool
    timeout::Int # seconds
    iterators::Vector{Any}
end

function synth(polys; kwargs...)
    polys = map(mkpoly, polys)

    solver  = get(kwargs, :solver, Yices)
    timeout = get(kwargs, :timeout, 10)
    maxsol  = get(kwargs, :maxsol, 1)
    trivial = get(kwargs, :trivial, false)

    syms = variables(polys)
    xparams, xvars = filtervars(syms)
    vars   = map(mkvar, get(kwargs, :vars, xvars))
    params = map(mkvar, get(kwargs, :params, xparams))
    @assert issubset(xvars, vars) "Variables in polys ($(xvars)) not a subset of given variables ($(vars))"

    shape = get(kwargs, :shape, full)
    # permutations of variables without dimension for constant 1
    constone = mkvar(:cc)
    perm = get(kwargs, :perm, shape in (uni, upper))
    perm_iter = perm ? VarPerm(copy(vars), constone) : [[copy(vars); constone]]
    # add dimension for constant 1
    push!(vars, constone)

    dims = length(vars)
    body = dynamicsmatrix(dims, shape)
    part_iter = get(kwargs, :part, shape == uni ? partitions(dims, 1) : partitions(dims))

    iters = [Iterators.product(part_iter, perm_iter)]

    Synthesizer{solver}(body, polys, vars, params, shape, maxsol, trivial, timeout, iters)
end

function synthfirst(polys; kwargs...)

    maxauxvars = get(kwargs, :maxauxvars, 1)

    polys = map(mkpoly, polys)
    syms = variables(polys)
    _, vars = filtervars(syms)
    args = Dict(collect(kwargs))
    progress = ProgressUnknown("Tries:")
    for _ in 1:maxauxvars
        push!(vars, gensym_unhashed(:t))
        args[:vars] = vars
        args[:timeout] = 1
        synthesizer = synth(polys; args...)
        for sol in synthesizer
            issat(sol) && return sol
            next!(progress)
        end
    end
    return nothing
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
    S.body[end,1:end-1] .= mkpoly(0)
    S.body[end,end] = mkpoly(1)
    # xvars = [vars; mkvar("cc")]
    init = initvec(vars, S.params)
    init[end,1:end-1] .= mkpoly(0)
    init[end,end] = mkpoly(1)
    ctx = mkcontext(S.body, init, S.polys, vars, S.params, roots)
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