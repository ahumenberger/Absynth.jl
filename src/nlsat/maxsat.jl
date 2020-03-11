function add_def(s::Solver, x::Z3Expr)
    name = bool_const(ctx(s), "$(id(x))")
    add(s, name == x)
    name
end

function relax_core(s::Solver, core::ExprVector, cs::Vector{<:Z3Expr})
    prefix = bool_val(ctx(s), true)
    for c in core
        deleteat!(cs, findfirst(isequal(c), cs))
    end
    for i in 1:length(core)-1
        prefix = add_def(s, and(core[i], prefix))
        push!(cs, add_def(s, or(prefix, core[i+1])))
    end
    cs
end

function maxsat(s::Solver, cs::Vector{<:Z3Expr})
    cost = 0
    cs0 = copy(cs)
    cs1 = copy(cs)
    push(s)
    while (res = check(s, cs1)) == Z3.unsat && cost < length(cs0)
        cost += 1
        cs1 = relax_core(s, unsat_core(s), cs1)
    end
    @debug "Maxsat" cost res==Z3.sat reason_unknown(s)
    satisfied = [c for c in cs0 if is_true(Z3.eval(get_model(s), c, false))]
    m = get_model(s)
    pop(s, 1)
    @debug "Maxsat" satisfied m
    res, m
end

