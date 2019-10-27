mutable struct SMTSolver{name} <: NLSolver
    vars::Dict{Symbol,Type}
    cs::ClauseSet
    
    function SMTSolver{name}() where {name}
        @assert exists(SMTSolver{name})
        @assert name isa Symbol
        new(Dict(), ClauseSet())
    end
end

SMTSolver(s::String) = SMTSolver{Symbol(s)}

program_name(::Type{SMTSolver{name}}) where {name} = string(name)
program_name(::T) where {T<:SMTSolver} = program_name(T)
exists(::Type{T}) where {T<:SMTSolver} = !isnothing(Sys.which(program_name(T)))

function variables!(s::SMTSolver, d::Dict{Symbol,Type})
    push!(s.vars, d...)
end

# ------------------------------------------------------------------------------

function tosmt(s::SMTSolver, x)
    expr = postwalk(preprocess_smt(x)) do sym
        if sym isa Number
            :(pysmt.Real(float($sym)))
        else
            get(pysmt_opmap, sym, sym)
        end
    end
end

tosmt(s::SMTSolver, c::Constraint{R}) where {R} = Expr(:call, pysmt_relmap[R], tosmt(s, c.poly), :(pysmt.Real(0)))
tosmt(s::SMTSolver, c::Clause) = Expr(:call, :(pysmt.Or), [tosmt(s, x) for x in c]...)
tosmt(s::SMTSolver, c::ClauseSet) = Expr(:call, :(pysmt.And), [tosmt(s, x) for x in c]...)

function write_smt2(io::IO, s::SMTSolver)
    ls = Expr[]
    for (var, type) in s.vars
        push!(ls, Expr(:(=), var, pysmt.Symbol(string(var), eval(pysmt_typemap[type]))))
    end
    expr = Expr(:block, ls..., tosmt(s, s.cs))
    pyexpr = eval(expr)

    write(io, "(set-option:produce-models true)\n")
    write(io, "(set-logic QF_NRA)\n")
    for (k,v) in s.vars
        t = eval(pysmt_typemap[v]).as_smtlib()
        write(io, "(declare-fun $k $t)\n")
    end
    write(io, "(assert ", pysmt.to_smtlib(pyexpr), ")\n")
    write(io, "(check-sat)")
    write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
end

function to_smtlib(s::SMTSolver)
    ptr = z3.SolverFor("QF_NRA")
    ls = Expr[]
    for (var, type) in s.vars
        push!(ls, Expr(:(=), var, z3_typemap[type](string(var))))
    end
    for cl in s.cs
        clause = if length(cl) == 1
            :($(preprocess_smt(convert(Expr, first(cl)))))
        else
            :(z3.Or($([preprocess_smt(convert(Expr, c)) for c in cl]...)))
        end
        expr = Expr(:block, ls..., clause)
        z3clause = eval(expr)
        ptr.add(z3clause)
    end
    ptr.to_smt2()
end

function write_vars(io::IO, s::SMTSolver)
    for (v,t) in s.vars
        write(io, "(declare-const $v Real)\n")
    end
end

function write_constraints(io, s::SMTSolver)
    write(io, smt(s.cs; expand_pow=true))
end

function write_smt(io::IO, s::SMTSolver)
    write(io, "(set-option:produce-models true)\n")
    write(io, "(set-logic QF_NRA)\n")
    write_vars(io, s)
    write_constraints(io, s)
    write(io, "(check-sat)")
    write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
end

function solve(s::SMTSolver; timeout::Int=-1)
    path, io = mktemp()
    write_smt(io, s)
    close(io)
    newpath = string(path, ".smt2")
    mv(path, newpath)
    try
        openproc(parse_smtoutput, `$(program_name(s)) $newpath`, timeout=timeout)
    finally
        # @info "" newpath
        rm(newpath)
    end
end
