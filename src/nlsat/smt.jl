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

preprocess_smt(x::Expr) = postwalk(x) do y
    @match y begin
        b_^e_ => Expr(:call, :*, fill(b, e)...)
        -b_    => :((-1)*$b)
        _     => y
    end
end

tosmt(s::SMTSolver, x::Number) = pysmt.Real(float(x))
tosmt(s::SMTSolver, x::Symbol) = :(pysmt.Symbol($(string(x)), $(pysmt_typemap[s.vars[x]]))) |> eval
tosmt(s::SMTSolver, x::Expr) = postwalk(preprocess_smt(x)) do sym
    if issymbol(sym)
        :(pysmt.Symbol($(string(sym)), $(pysmt_typemap[s.vars[sym]])))
    elseif sym isa Number
        :(pysmt.Real(float($sym)))
    else
        get(pysmt_opmap, sym, sym)
    end
end |> eval

tosmt(s::SMTSolver, c::Constraint{R}) where {R} = pysmt_relmap[R](tosmt(s, c.poly), pysmt.Real(0))
tosmt(s::SMTSolver, c::Clause) = pysmt.Or([tosmt(s, x) for x in c])
tosmt(s::SMTSolver, c::ClauseSet) = pysmt.And([tosmt(s, x) for x in c])

function write_smt(io::IO, s::SMTSolver)
    write(io, "(set-option:produce-models true)\n")
    write(io, "(set-logic QF_NRA)\n")
    for (k,v) in s.vars
        t = eval(pysmt_typemap[v]).as_smtlib()
        write(io, "(declare-fun $k $t)\n")
    end
    write(io, "(assert ", pysmt.to_smtlib(tosmt(s, s.cs)), ")\n")
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
        rm(newpath)
    end
end
