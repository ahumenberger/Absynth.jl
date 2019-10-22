mutable struct Z3Solver <: NLSolver
    ptr::PyObject
    vars::Dict{Symbol, PyObject}
    cs::ClauseSet
    cstr::Vector{PyObject}
    Z3Solver() = new(z3.SolverFor("QF_NRA"), Dict(), ClauseSet(), [])
end

function variables!(s::Z3Solver, d::Dict{Symbol,Type})
    for (var, type) in d
        push!(s.vars, var => z3_typemap[type](string(var)))
        if type == Rational
            p, q = gensym("p"), gensym("q")
            push!(s.vars, p => z3.Int(string(p)))
            push!(s.vars, q => z3.Int(string(q)))
            constraints!(s, [:($q > 0), :($p/$q == $(var))])
        end
    end
    s.vars
end

function set_constraints(s::Z3Solver)
    ls = Expr[]
    for (svar, z3var) in s.vars
        push!(ls, Expr(:(=), svar, z3var))
    end
    for cl in s.cs
        clause = if length(cl) == 1
            :($(convert(Expr, first(cl))))
        else
            :(z3.Or($([convert(Expr, c) for c in cl]...)))
        end
        expr = Expr(:block, ls..., clause)
        z3clause = eval(expr)
        s.ptr.add(z3clause)
        push!(s.cstr, z3clause)
    end
end

function solve(s::Z3Solver; timeout::Int=-1)
    mktemp() do path, io
        set_constraints(s)
        write(io, s.ptr.to_smt2())
        write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
        close(io)
        openproc(parse_smtoutput, `z3 $path`, timeout=timeout)
    end
end