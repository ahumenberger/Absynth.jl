mutable struct SMTSolver{name} <: NLSolver
    vars::Dict{Symbol,Type}
    cs::ClauseSet
    
    function SMTSolver{name}() where {name}
        @assert exists(SMTSolver{name})
        @assert name isa Symbol
        new(Dict(), ClauseSet())
    end
end

const SMTSolverZ3 = SMTSolver{:z3}
const SMTSolverYices = SMTSolver{:yices}

SMTSolver(s::String) = SMTSolver{Symbol(s)}

program_name(::Type{SMTSolver{name}}) where {name} = string(name)
program_name(::T) where {T<:SMTSolver} = program_name(T)
program_name(::SMTSolverYices) = "$(program_name(SMTSolverYices)) --logic=QF_NRA"

exists(::Type{T}) where {T<:SMTSolver} = !isnothing(Sys.which(program_name(T)))

fileext(::SMTSolver) = ".smt2"
parsefunc(::SMTSolver) = parse_output_smt
parsefunc(::SMTSolverYices) = parse_output_yices

add_vars!(s::SMTSolver, d::Dict{Symbol,Type}) = push!(s.vars, d...)
add!(s::SMTSolver, cs::ClauseSet) = s.cs &= cs

function write_header(io::IO, s::SMTSolver)
    write(io, "(set-option:produce-models true)\n")
    write(io, "(set-logic QF_NRA)\n")
end

function write_header(io::IO, s::SMTSolverZ3) end
function write_header(io::IO, s::SMTSolverYices) end

function write_vars(io::IO, s::SMTSolver)
    for (v,t) in s.vars
        write(io, "(declare-const $v Real)\n")
    end
end

function write_vars(io::IO, s::SMTSolverYices)
    for (v,t) in s.vars
        write(io, "(define $v::real)\n")
    end
end

function write_constraints(io::IO, s::SMTSolver)
    write(io, smt(s.cs; expand_pow=true), "\n")
end

function write_constraints(io::IO, s::Union{SMTSolverZ3,SMTSolverYices})
    write(io, smt(s.cs; expand_pow=false), "\n")
end

function write_footer(io::IO, s::SMTSolver)
    write(io, "(check-sat)\n")
    write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
end

function write_footer(io::IO, s::SMTSolverYices)
    write(io, "(check)\n")
    write(io, "(show-model)\n")
end

function write_problem(io::IO, s::T) where {T<:NLSolver}
    write_header(io, s)
    write_vars(io, s)
    write_constraints(io, s)
    write_footer(io, s)
end

function solve(s::SMTSolver; timeout::Int=-1)
    path, io = mktemp()
    write_problem(io, s)
    close(io)
    newpath = string(path, fileext(s))
    mv(path, newpath)
    try
        openproc(parsefunc(s), `$(split(program_name(s))) $newpath`, timeout=timeout)
    finally
        rm(newpath)
    end
end

# ------------------------------------------------------------------------------

function openproc(parse::Function, cmd::Cmd; timeout=-1)
    start = time_ns()
    P = open(pipeline(cmd, stderr=devnull))
    if timeout < 0
        wait(P)
    else
        timedwait(()->!process_running(P), float(timeout))
        if process_running(P)
            @debug "Kill"
            kill(P)
            close(P.in)
            return NLSat.timeout, Second(timeout), nothing
        end
    end
    elapsed = Millisecond(round((time_ns()-start)/1e6))

    if P.exitcode >= 0
        lines = readlines(P)
        status = popfirst!(lines)
        if status == "sat"
            d = parse(lines)
            return NLSat.sat, elapsed, d
        elseif status == "unsat"
            return NLSat.unsat, elapsed, nothing
        elseif status == "unknown"
            return NLSat.unknown, elapsed, nothing
        end

        error("Unknown status: $status")
    end
    return NLSat.unknown, elapsed, nothing
end

function parse_output_smt(s::Array{String})
    m = NLModel()
    sexpr = parse_sexpr(join(s))
    for x in sexpr.vec
        @assert length(x.vec) == 2
        sym = x.vec[1]
        val = try_int(eval(to_expr(x.vec[2])))
        push!(m, sym=>val)
    end
    m
end

function parse_output_yices(s::Array{String})
    m = NLModel()
    sexpr = parse_sexpr(string("(", join(s), ")"))
    for x in sexpr.vec
        @assert length(x.vec) == 3 && x.vec[1] == :(=) "$x"
        sym = x.vec[2]
        val = try_int(eval(to_expr(x.vec[3])))
        push!(m, sym=>val)
    end
    m
end

try_int(x) = x === NaN ? x : isinteger(x) ? convert(Int, x) : rationalize(x)

Base.rationalize(x::Rational) = x