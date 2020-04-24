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

const Partition = Vector{Vector{Int}}

g_partition_history = Vector{Partition}()
g_solutions = Vector{Partition}()


function move_iterator(P::Partition, set_idx, elem)
    # elem = P[set_idx][elem_idx]
    P = deepcopy(P)
    deleteat!(P[set_idx], findfirst(x->x==elem, P[set_idx]))
    iter = ([
        (if i == j
            [Y; elem]
        else
            Y
        end) for (j, Y) in enumerate(P)
    ] for i = 1:length(P) if i != set_idx)
    (i for i in iter if !(i in g_partition_history))
end

function learn_partitions(ms, us, partition, partition_map, core)
    @info "Learn next partitions" string(partition) partition_map core
    
        
        Iterators.flatten((if is_eq(x)
            # @info "" partition_map[id(x)]
            (p1, i1), (p2, i2) = partition_map[id(x)]
            # index1, index2 = partition[p1][i1], partition[p2][i2]
            it1 = move_iterator(partition, p1, i1)
            it2 = move_iterator(partition, p2, i2)
            Iterators.flatten((it1, it2))
        elseif is_distinct(x)

        else
            error("No equality/inequality: $(x)")
        end for x in core))
end

function solve_constraints(s::Solver, mss, uss, partitions, current=1)
    push(s)
    ms, us, partition = mss[current], uss[current], partitions[current]
    assumptions = Z3Expr[]
    partition_map = Dict{UInt32, Pair{Pair{Int,Int},Pair{Int,Int}}}()
    for (t, indices) in enumerate(partition)
        usum = us[indices[1]]
        for i = 2:length(indices)
            j, k = indices[i-1], indices[i]
            ass = (ms[j] == ms[k])
            push!(assumptions, ass)
            usum += us[k]
            @assert !haskey(partition_map, id(ass))
            partition_map[id(ass)] = (t=>j) => (t=>k)
        end
        add(s, usum == 0)
        if t > 1
            j, k = first(partition[t-1]), first(indices)
            ass = ms[j] != ms[k]
            push!(assumptions, ass)
            @assert !haskey(partition_map, id(ass))
            partition_map[id(ass)] = (t-1=>j) => (t=>k)
        end
    end

    # x = Base.unique(Iterators.flatten(collect(Iterators.product(X, X)) for X in Iterators.product(partition...)))
    # xx = []
    # for (i, (a, b)) in enumerate(x)
    #     @info "" a b a == b (b,a) in x
    #     if a != b && !((b, a) in xx)
    #         push!(xx, (a,b))
    #         ass = ms[a] != ms[b]
    #         push!(assumptions, ass)
    #         # @assert !haskey(partition_map, id(ass))
    #         # partition_map[id(ass)] = (t-1=>j) => (t=>k)
    #     end
    # end

    @debug "Assumptions" assumptions
    res = check(s, assumptions)
    push!(g_partition_history, partition)
    if res == Z3.sat
        if current == length(mss)
            # for (i,(m,u)) in enumerate(zip(mss[1], uss[1]))
            #     @info "Term $i" m u
            # end
            # @info "" assumptions get_model(s)
            for a in assumptions
                add(s, a)
            end
            # println(s)
            @info "" check(s) == Z3.sat get_model(s)
            # @info "" get_model(s) mss uss
            return true
        end
        for a in assumptions
            add(s, a)
        end
        @info "Next constraint" s
        return solve_constraints(s, mss, uss, partitions, current+1)
    elseif res == Z3.unsat
        @info "UNSAT"
        for ps in learn_partitions(ms, us, partition, partition_map, unsat_core(s))
            # @info "" ps
            parts = deepcopy(partitions)
            parts[current] = ps
            # @info "Next partition" s
            pop(s, 1)
            solve_constraints(s, mss, uss, parts, current) && return true
        end
        return false
    else
        error("Z3 unknown: $(reason_unknown(s))")
    end
end

function check_cfinite(s::CFiniteSolver, z3::Solver, vars, soft_clauses)
    uss = [[Z3Expr(ctx(z3), vars, x) for x in c[1].us] for c in soft_clauses]
    mss = [[Z3Expr(ctx(z3), vars, x) for x in c[1].ms] for c in soft_clauses]

    soft_clauses = Z3Expr[u == 0 for u in Iterators.flatten(uss)]
    @debug "Soft clauses" soft_clauses

    res, model = maxsat(z3, soft_clauses)
    res != Z3.sat && return res # hard clauses not satisfiable or timeout
    partitions = [collect(find_partition(model, ms)) for ms in mss]
    solve_constraints(z3, mss, uss, partitions) && return Z3.sat
    Z3.unsat
end

function solve(s::CFiniteSolver; timeout::Int=-1)
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

    elapsed_sec = @elapsed res = check_cfinite(s, z3, z3vars, sclauses)
    @debug "CFiniteSolver" res == Z3.sat reason_unknown(z3)
    elapsed = Millisecond(round(elapsed_sec*1000))
    if res == Z3.sat
        return NLSat.sat, elapsed, parse_model(get_model(z3))
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