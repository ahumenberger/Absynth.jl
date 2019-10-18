import Base: iterate

closedform_systems(rt::RecurrenceTemplate, iter) =
    (ClosedFormTemplate(rt, part) for part in (isnothing(iter) ? partitions(size(rt)) : iter))

# TODO: How to deal with templates where a permutation is useless?
recurrence_systems(vars::Vector{Symbol}, shape::MatrixShape, iter=permutations(vars); kwargs...) =
    (RecurrenceTemplate(perm, shape; kwargs...) for perm in (isnothing(iter) ? permutations(vars) : iter))

synthesis_problems(inv::Invariant, recsys_iter, part_iter; kwargs...) = 
    (SynthesisProblem(inv, r, c) for r in recsys_iter for c in closedform_systems(r, part_iter))

synthesis_problems(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape, perm_iter, part_iter; kwargs...) =
    synthesis_problems(inv, recurrence_systems(vars, shape, perm_iter; kwargs...), part_iter)

# ------------------------------------------------------------------------------

# TODO: Find better names for strategies

function strategy_permutation(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape; kwargs...)
    @assert shape == UpperTriangular || shape == UnitUpperTriangular
    synthesis_problems(inv, vars, shape, nothing, nothing; kwargs...)
end

function strategy_fixed(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape; kwargs...)
    rec = RecurrenceTemplate(vars, shape; kwargs...)
    synthesis_problems(inv, [rec], nothing; kwargs...)
end

function strategy_fixed2(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape, roots::Vector{Int}; kwargs...)
    rec = RecurrenceTemplate(vars, shape; kwargs...)
    synthesis_problems(inv, [rec], [roots]; kwargs...)
end

# ------------------------------------------------------------------------------

struct Solutions
    solver::NLSolver
    problem::SynthesisProblem
    maxsol::Number
    timeout::Int

    function Solutions(p::SynthesisProblem; maxsol::Number=1, timeout::Int=2, solver::Type{<:NLSolver}=Z3)
        @assert maxsol >= 1
        new(create_solver(p, solver), p, maxsol, timeout)
    end
end

iterate(ms::Solutions) = iterate(ms, 0)

function iterate(ms::Solutions, state)
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

solutions(strategy; kwargs...) =
    Iterators.flatten(Solutions(problem; kwargs...) for problem in strategy)

models(strategy; kwargs...) =
    Iterators.filter(Absynth.issat, solutions(strategy; kwargs...))
