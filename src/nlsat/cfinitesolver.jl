include("maxsat.jl")

mutable struct CFiniteSolver <: NLSolver
    vars::Dict{Symbol,Type}
    hard_clauses::ClauseSet
    cfin_clauses::ClauseSet
    soft_clauses::ClauseSet
    function CFiniteSolver()
        new(Dict(), ClauseSet(), ClauseSet(), ClauseSet())
    end
end

function add!(s::CFiniteSolver, cs::ClauseSet)
    for c in cs
        if length(c) == 1 && first(c) isa CFiniteConstraint{EQ}
            s.cfin_clauses &= c
            # limit = min(3, length(first(c).us))
            s.hard_clauses &= expand(first(c), 1)
        else
            cl = Clause()
            for cstr in c
                cl |= expand(cstr)
            end
            s.hard_clauses &= cl
        end
    end
end
add_soft!(s::CFiniteSolver, cs::ClauseSet) = s.soft_clauses &= cs
add_vars!(s::CFiniteSolver, d::Dict{Symbol,Type}) = push!(s.vars, d...)

# ------------------------------------------------------------------------------

const Partition = Vector{Vector{Int}}
const SPartition = Set{Set{Int}}

struct PartitionManager
    stack::Stack{Partition}
    history::Set{SPartition}
    unsat_cores::Vector{SPartition}
end

PartitionManager() = PartitionManager(Stack{Partition}(), Set{SPartition}(), Vector{SPartition}())

function _already_visited(m::PartitionManager, P::Partition)
    S = Set(Set(x) for x in P)
    for core in m.unsat_cores
        if issubset(core, S)
            return true
        end
    end
    S in m.history
end
function _visit!(m::PartitionManager, P::Partition)
    S = Set(Set(x) for x in P)
    push!(m.history, S)
end

# function backtrack!(m::PartitionManager, level::Integer)
#     for i in level+1:length(m.stacks)
#         empty!(g_partition_histories[i])
#         empty!(g_partition_stacks[i])
#     end
# end

function Base.pop!(m::PartitionManager)
    while true
        isempty(m.stack) && return nothing
        P = pop!(m.stack)
        if !_already_visited(m, P)
            _visit!(m, P)
            return P
        end
    end
end

function Base.push!(m::PartitionManager, iter)
    for P in iter
        push!(m, P)
    end
end

function Base.push!(m::PartitionManager, P::Partition)
    push!(m.stack, P)
end

function learn_core!(m::PartitionManager, C::SPartition)
    @debug "learn $C"
    push!(m.unsat_cores, C)
end

# ------------------------------------------------------------------------------

function find_partition(model::Model, ms)
    ps = Dict{Z3Expr,Vector{Int}}()
    for (i, m) in enumerate(ms)
        mval = Z3.eval(model, m, false)
        if haskey(ps, mval)
            push!(ps[mval], i)
        else
            push!(ps, mval=>Int[i])
        end
    end
    values(ps)
end

function move_iterator(P::Partition, set_idx, elem)
    P = deepcopy(P)
    deleteat!(P[set_idx], findfirst(x->x==elem, P[set_idx]))
    deleteat!(P, findall(x->isempty(x), P))
    iter = ([
        (if i == j
            [Y; elem]
        else
            Y
        end) for (j, Y) in enumerate(P)
    ] for i = 1:length(P) if i != set_idx)
    # (i for i in iter if !already_visited(i))
    # @debug "" P elem [P; [[elem]]]
    Iterators.flatten((iter, [[P; [[elem]]]]))
end

function distinct_iterator(P::Partition, idx1, elem1, idx2, elem2)
    # display(P)
    P = deepcopy(P)
    deleteat!(P[idx1], findfirst(x->x==elem1, P[idx1]))
    deleteat!(P[idx2], findfirst(x->x==elem2, P[idx2]))
    deleteat!(P, findall(x->isempty(x), P))
    iter = ([
        (if i == j
            [Y; elem1; elem2]
        else
            Y
        end) for (j, Y) in enumerate(P)
    ] for i = 1:length(P))
    # (i for i in iter if !already_visited(i))
    iter
end

function learn_partitions(ms, us, partition, partition_map, core)
    # @debug "Learn next partitions" string(partition) partition_map core
    Iterators.flatten((if is_eq(x)
        # @debug "" partition_map[id(x)]
        (p1, i1), (p2, i2) = partition_map[id(x)]
        # index1, index2 = partition[p1][i1], partition[p2][i2]
        it1 = move_iterator(partition, p1, i1)
        it2 = move_iterator(partition, p2, i2)
        Iterators.flatten((it1, it2))
    elseif is_distinct(x)
        (p1, i1), (p2, i2) = partition_map[id(x)]
        x = distinct_iterator(partition, p1, i1, p2, i2)
        @debug "" collect(x) p1 i1 p2 i2
        x
    else
        error("No equality/inequality: $(x)")
    end for x in core))
end

function solve_constraints(s::Solver, mss, uss, partitions, current=1)
    @debug("Number of constraints to solve: $(length(mss))")
    @debug "" partitions
    m = PartitionManager()
    push!(m, partitions[current])
    # push(s)
    while true
        push(s)
        @debug "New iteration at level: $current ======================================="
        partition = pop!(m)
        isnothing(partition) && return false

        ms, us = mss[current], uss[current]
        assumptions = Z3Expr[]
        usums = Z3Expr[]
        partition_map = Dict{UInt32, Pair{Pair{Int,Int},Pair{Int,Int}}}()
        for (t, indices) in enumerate(partition)
            usum = us[indices[1]]
            # all m in one set of partition are equal
            for i = 2:length(indices)
                j, k = indices[i-1], indices[i]
                ass = (ms[j] == ms[k])
                push!(assumptions, ass)
                usum += us[k]
                @assert !haskey(partition_map, id(ass))
                partition_map[id(ass)] = (t=>j) => (t=>k)
            end
            # the sum of all u in one set of partition has to be 0
            push!(usums, usum == 0)
            # if there is more than one set in the partition, 
            # then the m in different sets have to be different 
            if t > 1
                j, k = first(partition[t-1]), first(indices)
                ass = ms[j] != ms[k]
                push!(assumptions, ass)
                @assert !haskey(partition_map, id(ass))
                partition_map[id(ass)] = (t-1=>j) => (t=>k)
            end
        end

        for su in usums
            add(s, su)
        end
        res = check(s, assumptions)
        @debug "Assumptions" string(partition) usums assumptions res == Z3.unsat unsat_core(s)
        if res == Z3.unsat && length(unsat_core(s)) == 0
            pop(s, 1)
            res = check(s, usums)
            @debug "" res == Z3.unknown reason_unknown(s)
            @assert res == Z3.unsat
            core = unsat_core(s)
            pcore = SPartition(Set{Int}(partition[findfirst(x->isequal(x, ex), usums)]) for ex in core)
            learn_core!(m, pcore)
            core_indices = (findfirst(x->isequal(x, ex), usums) for ex in core)
            Ps = (move_iterator(partition, i, elem) for i in core_indices for elem in partition[i])
            push!(m, Iterators.flatten(Ps))
        elseif res == Z3.sat
            if current == length(mss)
                # all C-finite constraints are satisfied
                # add assumptions to get back values for Z3
                # TODO: is this really needed?
                for a in assumptions
                    add(s, a)
                end
                check(s)
                @debug "" check(s) == Z3.sat get_model(s)
                return true
            else
                # there are C-finite constraints left; continue with current+1
                for a in assumptions
                    add(s, a)
                end
                solve_constraints(s, mss, uss, partitions, current+1) && return true
                pop(s, 1)
            end
        elseif res == Z3.unsat
            Ps = learn_partitions(ms, us, partition, partition_map, unsat_core(s)) |> collect
            push!(m, Ps)
            pop(s, 1)
        else
            return false
        end
    end
end

function check_cfinite(s::CFiniteSolver, z3::Solver, vars, soft_clauses)
    uss = [[Z3Expr(ctx(z3), vars, x) for x in first(c).us] for c in soft_clauses]
    mss = [[Z3Expr(ctx(z3), vars, x) for x in first(c).ms] for c in soft_clauses]

    soft_clauses = Z3Expr[u == 0 for u in Iterators.flatten(uss)]
    @debug "Soft clauses" soft_clauses

    res, cost, model = maxsat(z3, soft_clauses)

    res == Z3.sat && iszero(cost) && return Z3.sat, model # soft clauses are all satisfiable
    res != Z3.sat && return res, nothing                  # hard clauses not satisfiable or timeout

    partitions = [collect(find_partition(model, ms)) for ms in mss]
    solve_constraints(z3, mss, uss, partitions) && return Z3.sat, get_model(z3)

    return Z3.unsat, nothing
end

function solve(s::CFiniteSolver; timeout::Int=-1)
    @debug("Solve")
    set_param("unsat_core", true)
    ctx = main_ctx()
    if timeout > 0
        set(ctx, "timeout", timeout*1000)
    end
    z3 = mk_solver()
    # add variables
    z3vars = Dict{Symbol,Z3Expr}()
    for (k,v) in s.vars
        push!(z3vars, k=>real_const(ctx, string(k)))
    end
    # add hard clauses
    for cl in s.hard_clauses
        add(z3, Z3Expr(ctx, z3vars, cl))
    end
    @debug "" [length(first(cl).us) for cl in s.cfin_clauses]
    # C-finite clauses
    sclauses = ClauseSet()
    for cl in s.cfin_clauses
        # if clause consists of just one term then add it as a hard clause
        if length(first(cl).us) == 1
            add(z3, Z3Expr(ctx, z3vars, first(cl).us[1]) == 0)
        else
            push!(sclauses, cl)
        end
    end

    elapsed_sec = @elapsed res, model = check_cfinite(s, z3, z3vars, sclauses)
    @debug "CFiniteSolver" res == Z3.sat reason_unknown(z3)
    elapsed = Millisecond(round(elapsed_sec*1000))
    if res == Z3.sat
        return NLSat.sat, elapsed, parse_model(model)
    elseif res == Z3.unsat
        return NLSat.unsat, elapsed, nothing
    elseif res == Z3.unknown
        reason = reason_unknown(z3)
        if reason == "timeout"
            return NLSat.timeout, elapsed, nothing
        end
        return NLSat.unknown, elapsed, nothing
    end
end