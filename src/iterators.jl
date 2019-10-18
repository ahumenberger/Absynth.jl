import Base: iterate

closedform_systems(rt::RecurrenceTemplate) =
    (ClosedFormTemplate(rt, part) for part in partitions(size(rt)))

# TODO: How to deal with templates where a permutation is useless?
recurrence_systems(vars::Vector{Symbol}, shape::MatrixShape; kwargs...) =
    (RecurrenceTemplate(perm, shape; kwargs...) for perm in permutations(vars))

# ------------------------------------------------------------------------------

# TODO: Find better names for strategies

_strategy(inv, recsystems, partitions) = 
    (SynthesisProblem(inv, first(args), ClosedFormTemplate(args...)) for args in Iterators.product(recsystems, partitions))

function strategy_permutation(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape; params::Vector{Symbol}=Symbol[])
    @assert shape == UpperTriangular || shape == UnitUpperTriangular
    part = partitions(length(vars))
    recs = recurrence_systems(vars, shape; params=params)
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

# ------------------------------------------------------------------------------

function _run(strategy, solver::Type{<:NLSolver}, timeout::Int, maxsol::Number)
    Iterators.flatten(Models(problem, solver, maxsol, timeout) for problem in strategy)
end

function run(strategy; solver::Type{<:NLSolver}=Z3, timeout::Int=2, maxsol::Number=1)
    foreach(display, _run(strategy, solver, timeout, maxsol))
end
