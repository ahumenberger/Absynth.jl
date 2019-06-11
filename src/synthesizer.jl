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
    info::SynthInfo
    maxsol::Number

    function Solutions(s::NLSolver, info::SynthInfo; maxsol=Inf)
        @assert maxsol >= 1
        new(s, info, maxsol)
    end
end

IteratorSize(::Type{Solutions}) = HasLength()
Base.length(s::Solutions) = s.maxsol

iterate(it::Solutions) = iterate(it, 0)

function iterate(s::Solutions, state)
    if isnothing(state) || state >= s.maxsol
        return nothing
    end
    status, elapsed, model = NLSat.solve(s.solver, timeout=s.info.timeout)
    if status == NLSat.sat
        A, B = s.info.ctx.init, s.info.ctx.body
        body = [get(model, Symbol(string(b)), b) for b in B]
        init = [get(model, Symbol(string(b)), b) for b in A]
        next_constraints!(s.solver, model)
        return SynthResult(Loop(init, body), elapsed, s.info), state+1
    end
    SynthResult(status, elapsed, s.info), nothing
end

function next_constraints!(s::NLSolver, m::Model)
    cs = [:($var != $val) for (var, val) in m]
    constraints!(s, [or(cs...)])
end

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