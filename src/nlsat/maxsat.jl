# def add_def(s, fml):
#     name = Bool("%s" % fml)
#     s.add(name == fml)
#     return name

# def relax_core(s, core, Fs):
#     prefix = BoolVal(True)
#     Fs -= { f for f in core }
#     for i in range(len(core)-1):
#         prefix = add_def(s, And(core[i], prefix))
#         Fs |= { add_def(s, Or(prefix, core[i+1])) }

# def maxsat(s, Fs):
#     cost = 0
#     Fs0 = Fs.copy()
#     while unsat == s.check(Fs):
#         cost += 1
#         relax_core(s, s.unsat_core(), Fs)    
#     return cost, { f for f in Fs0 if tt(s, f) }

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
        cs = [or(c, add_def(s, or(prefix, core[i+1]))) for c in cs]
    end
    cs
end

function maxsat(s::Solver, cs::Vector{<:Z3Expr})
    cost = 0
    cs0 = copy(cs)
    while check(s, cs) == Z3.unsat
        cost += 1
        cs = relax_core(s, unsat_core(s), cs)
    end
    cost, [c for c in cs0 if is_true(Z3.eval(get_model(s), c, false))]
end
