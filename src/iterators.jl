import Base: iterate

closedform_systems(rt::RecurrenceTemplate, iter) =
    (ClosedFormTemplate(rt, part) for part in (isnothing(iter) ? partitions(size(rt)) : iter))

# TODO: How to deal with templates where a permutation is useless?
recurrence_systems(vars::Vector{Symbol}, shape::MatrixShape, iter=permutations(vars); kwargs...) =
    (RecurrenceTemplate(copy(perm), shape; kwargs...) for perm in (isnothing(iter) ? permutations(vars) : iter))

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
    rec = RecurrenceTemplate(copy(vars), shape; kwargs...)
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

abstract type AbstractPermutations end
struct AllPermutations <: AbstractPermutations
    vars::Vector{Symbol}
end
struct FixedPermutations <: AbstractPermutations
    perms::Vector{Vector{Symbol}}
end

FixedPermutations(ps::Vector{Symbol}...) = FixedPermutations(collect(ps))

perms(p::AllPermutations) = Combinatorics.permutations(p.vars)
perms(p::FixedPermutations) = p.perms

function permutations(r::RecTemplate, p::AbstractPermutations)
    if has_constant_one(r)
        return ([vs; CONST_ONE_SYM] for vs in perms(p))
    end
    return perms(p)
end

Base.summary(io::IO, p::AllPermutations; uppercase=true) = print(io, uppercase ? "A" : "a", "ll permutations of $(p.vars)")
Base.summary(io::IO, p::FixedPermutations; uppercase=true) = print(io, uppercase ? "F" : "f", "ixed permutations $(p.perms)")
Base.show(io::IO, p::AbstractPermutations) = summary(io, p)


abstract type AbstractPartitions end
struct AllPartitions <: AbstractPartitions
    n::Int
end
struct FixedPartitions <: AbstractPartitions
    parts::Vector{Vector{Int}}
end

FixedPartitions(ps::Vector{Int}...) = FixedPartitions(collect(ps))

partitions(p::AllPartitions) = Combinatorics.partitions(p.n)
partitions(p::FixedPartitions) = p.parts

Base.summary(io::IO, p::AllPartitions; uppercase=true) = print(io, uppercase ? "A" : "a", "ll integer partitions of $(p.n)")
Base.summary(io::IO, p::FixedPartitions; uppercase=true) = print(io, uppercase ? "F" : "f", "ixed partitions $(p.parts)")
Base.show(io::IO, p::AbstractPartitions) = summary(io, p)

# ------------------------------------------------------------------------------

abstract type AbstractStrategy end

solutions(s::AbstractStrategy; kwargs...) = solutions(synthesis_problems(s); kwargs...)
models(s::AbstractStrategy; kwargs...) = models(synthesis_problems(s); kwargs...)

struct Strategy <: AbstractStrategy
    inv::Invariant
    rec::RecTemplate
    perms::AbstractPermutations
    parts::AbstractPartitions

    function Strategy(inv::Invariant, rec::RecTemplate; perms::AbstractPermutations, parts::AbstractPartitions)
        inv_vars = program_variables(inv)
        rec_vars = variables(rec)
        @assert issubset(inv_vars, rec_vars)
        new(inv, rec, perms, parts)
    end
end

synthesis_problems(s::Strategy) =
    synthesis_problems(s.inv, recurrence_systems(s.rec, permutations(s.rec, s.perms)), partitions(s.parts))

recurrence_systems(r::RecTemplate, perms) =
    (RecurrenceTemplate(r, copy(p)) for p in perms)

function Base.show(io::IO, s::Strategy)
    compact = get(io, :compact, false)
    # if compact
        print(io, "$(typeof(s)) with ")
        summary(io, s.perms, uppercase=false)
        print(io, " and ")
        summary(io, s.parts, uppercase=false)
    # else
        # print(io, "$(typeof(r)) for some permutation σ of $(vars)")
    # end
end

struct CombinedStrategy <: AbstractStrategy
    ls::Vector{Strategy}

    CombinedStrategy(ls::Strategy...) = new(collect(ls))
end

synthesis_problems(s::CombinedStrategy) = 
    Iterators.flatten(synthesis_problems(t) for t in s.ls)


function IterativeStrategy(inv::Invariant; constant_one::Bool=true)
    vars = program_variables(inv)
    size = constant_one ? length(vars)+1 : length(vars)
    rec1 = RecTemplate(copy(vars), constant_one=constant_one, shape=UnitUpperTriangular)
    str1 = Strategy(inv, rec1, perms=AllPermutations(vars), parts=FixedPartitions([size]))
    rec2 = RecTemplate(copy(vars), constant_one=constant_one, shape=UpperTriangular)
    str2 = Strategy(inv, rec2, perms=AllPermutations(vars), parts=AllPartitions(size))
    rec3 = RecTemplate(copy(vars), constant_one=constant_one, shape=FullSymbolic)
    str3 = Strategy(inv, rec3, perms=FixedPermutations(vars), parts=AllPartitions(size))
    return CombinedStrategy(str1, str2, str3)
end

# ------------------------------------------------------------------------------

struct Solutions
    solver::NLSolver
    problem::SynthesisProblem
    maxsol::Number
    timeout::Int

    function Solutions(p::SynthesisProblem; maxsol::Number=1, timeout::Int=2, solver::Type{<:NLSolver}=Z3Solver, constraints::ClauseSet=ClauseSet())
        @assert maxsol >= 1
        s = create_solver(p, solver)
        add!(s, constraints)
        new(s, p, maxsol, timeout)
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
    cs = Clause([Constraint{NEQ}(:($v - ($(numerator(m[v])) / $(denominator(m[v]))))) for v in vs])
    add!(s, ClauseSet(cs))
end

# ------------------------------------------------------------------------------

solutions(strategy; kwargs...) =
    Iterators.flatten(Solutions(problem; kwargs...) for problem in strategy)

models(strategy; kwargs...) =
    Iterators.filter(Absynth.issat, solutions(strategy; kwargs...))

function synth(inv::Invariant; timeout=2, solver=Z3Solver, constant_one=true, kwargs...)
    progress = ProgressUnknown("I'm trying hard:")
    strategy = IterativeStrategy(inv; constant_one=constant_one)
    for s in solutions(strategy; maxsol=1, timeout=timeout, solver=solver)
        if issat(s)
            finish!(progress)
            return s.recsystem
        end
        next!(progress)
    end
    finish!(progress)
end