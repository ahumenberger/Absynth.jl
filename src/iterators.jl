import Base: iterate

struct ClosedForms
    rt::RecurrenceTemplate
    part
end

function iterate(cf::ClosedForms)
    p, next = iterate(cf.part)
    ClosedFormTemplate(cf.rt, p), next
end

function iterate(cf::ClosedForms, state)
    s = iterate(cf.part, state)
    s === nothing && return
    ClosedFormTemplate(cf.rt, first(s)), last(s)
end

closedforms(rt::RecurrenceTemplate) = ClosedForms(rt, partitions(size(rt)))

# ------------------------------------------------------------------------------

struct RecSysIter
    perm
    kwargs
end

function iterate(it::RecSysIter)
    vars, next = iterate(it.perm)
    RecurrenceTemplate(vars; it.kwargs...), next
end

function iterate(it::RecSysIter, state)
    s = iterate(it.perm, state)
    s === nothing && return
    RecurrenceTemplate(first(s); it.kwargs...), last(s)
end

# TODO: How to deal with templates where a permutation is useless?
recurrence_systems(vars::Vector{Symbol}; kwargs...) =
    RecSysIter(permutations(vars), kwargs)

# ------------------------------------------------------------------------------

_strategy(inv, recsystems, partitions) = 
    (SynthesisProblem(inv, first(args), ClosedFormTemplate(args...)) for args in Iterators.product(recsystems, partitions))

function strategy_permutation(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape; params::Vector{Symbol}=Symbol[])
    @assert shape == UpperTriangular || shape == UnitUpperTriangular
    part = partitions(length(vars))
    recs = recurrence_systems(vars)
    _strategy(inv, recs, part)
end

function strategy_fixed(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape; params::Vector{Symbol}=Symbol[])
    part = partitions(length(vars))
    recs = [RecurrenceTemplate(vars, shape; params=params)]
    _strategy(inv, recs, part)
end

# ------------------------------------------------------------------------------

struct Models
    solver::NLSolver
    problem::SynthesisProblem
    maxsol::Number
    timeout::Int

    function Models(p::SynthesisProblem, solver::Type{<:NLSolver}, maxsol::Number, timeout::Int)
        @assert maxsol >= 1
        new(create_solver(p, solver), p, maxsol, timeout)
    end
end

models(p::SynthesisProblem; maxsol::Number=Inf, timeout::Int=10, solver::Type{<:NLSolver}=Z3) =
    Models(p, solver, maxsol, timeout)

iterate(ms::Models) = iterate(ms, 0)

function iterate(ms::Models, state)
    (state === nothing || state >= ms.maxsol) && return
    model, result = solve(ms.problem, ms.solver, timeout=ms.timeout)
    model === nothing && return result, nothing
    next_constraints!(ms.solver, ms.problem, model)
    result, state+1
end

function next_constraints!(s::NLSolver, sp::SynthesisProblem, m::NLModel)
    vs = [Symbol(string(v)) for v in body(sp) if !isconstant(v)]
    cs = Clause([Constraint{NEQ}(:($v - $(m[v]))) for v in vs])
    constraints!(s, ClauseSet(cs))
end