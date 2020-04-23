using Z3

mutable struct Z3Solver <: NLSolver
    vars::Dict{Symbol,Type}
    hard_clauses::ClauseSet
    soft_clauses::ClauseSet
    function Z3Solver()
        new(Dict(), ClauseSet(), ClauseSet())
    end
end

function add!(s::Z3Solver, cs::ClauseSet)
    s.hard_clauses &= expand(cs)
end
add_soft!(s::Z3Solver, cs::ClauseSet) = s.soft_clauses &= cs
add_vars!(s::Z3Solver, d::Dict{Symbol,Type}) = push!(s.vars, d...)

# ------------------------------------------------------------------------------

function solve(s::Z3Solver; timeout::Int=-1)
    ctx = main_ctx()
    if timeout > 0
        set(ctx, "timeout", timeout*1000)
    end
    z3vars = Dict{Symbol,Z3Expr}()
    for (k,v) in s.vars
        push!(z3vars, k=>real_const(ctx, string(k)))
    end
    
    z3 = mk_solver()
    for cl in s.hard_clauses
        add(z3, Z3Expr(ctx, z3vars, cl))
    end

    elapsed_sec = @elapsed res = check(z3)
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