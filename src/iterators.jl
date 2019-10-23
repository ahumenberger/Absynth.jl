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

function strategy_all(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape; kwargs...)
    @assert shape == UpperTriangular || shape == UnitUpperTriangular || shape == UserSpecific
    synthesis_problems(inv, vars, shape, nothing, nothing; kwargs...)
end

function strategy_permutations(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape, roots::Vector{Int}; kwargs...)
    @assert shape == UpperTriangular || shape == UnitUpperTriangular || shape == UserSpecific
    synthesis_problems(inv, vars, shape, nothing, [roots]; kwargs...)
end

function strategy_partitions(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape; kwargs...)
    rec = RecurrenceTemplate(vars, shape; kwargs...)
    synthesis_problems(inv, [rec], nothing; kwargs...)
end

function strategy_fixed(inv::Invariant, vars::Vector{Symbol}, shape::MatrixShape, roots::Vector{Int}; kwargs...)
    rec = RecurrenceTemplate(vars, shape; kwargs...)
    synthesis_problems(inv, [rec], [roots]; kwargs...)
end

strategy_mixed(inv::Invariant, vars::Vector{Symbol}; kwargs...) =
    Iterators.flatten([
        strategy_all(inv, vars, UnitUpperTriangular; kwargs...),
        strategy_all(inv, vars, UpperTriangular; kwargs...),
        strategy_partitions(inv, vars, FullSymbolic; kwargs...)
    ])

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

function synth(inv::Invariant; timeout=2, solver=Z3, kwargs...)
    progress = ProgressUnknown("I'm trying hard:")
    strategy = strategy_mixed(inv, program_variables(inv); kwargs...)
    for s in solutions(strategy; maxsol=1, timeout=timeout, solver=solver)
        if issat(s)
            finish!(progress)
            return s.recsystem
        end
        next!(progress)
    end
    finish!(progress)
end