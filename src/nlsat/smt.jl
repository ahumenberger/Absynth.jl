mutable struct SMTSolver{name} <: NLSolver
    vars::Dict{Symbol,Type}
    cs::ClauseSet
    
    function SMTSolver{name}() where {name}
        @assert exists(SMTSolver{name})
        @assert name isa Symbol
        new(Dict(), ClauseSet())
    end
end

const Z3Solver = SMTSolver{:z3}
const YicesSolver = SMTSolver{:yices}

SMTSolver(s::String) = SMTSolver{Symbol(s)}

program_name(::Type{SMTSolver{name}}) where {name} = string(name)
program_name(::T) where {T<:SMTSolver} = program_name(T)
program_name(::YicesSolver) = "$(program_name(YicesSolver)) --logic=QF_NRA"

exists(::Type{T}) where {T<:SMTSolver} = !isnothing(Sys.which(program_name(T)))

fileext(::SMTSolver) = ".smt2"
parsefunc(::SMTSolver) = parse_output_smt
parsefunc(::YicesSolver) = parse_output_yices

function variables!(s::SMTSolver, d::Dict{Symbol,Type})
    push!(s.vars, d...)
end

function write_header(io::IO, s::SMTSolver)
    write(io, "(set-option:produce-models true)\n")
    write(io, "(set-logic QF_NRA)\n")
end

function write_header(io::IO, s::Z3Solver) end
function write_header(io::IO, s::YicesSolver) end

function write_vars(io::IO, s::SMTSolver)
    for (v,t) in s.vars
        write(io, "(declare-const $v Real)\n")
    end
end

function write_vars(io::IO, s::YicesSolver)
    for (v,t) in s.vars
        write(io, "(define $v::real)\n")
    end
end

function write_constraints(io::IO, s::SMTSolver)
    write(io, smt(s.cs; expand_pow=true), "\n")
end

function write_constraints(io::IO, s::Union{Z3Solver,YicesSolver})
    write(io, smt(s.cs; expand_pow=false), "\n")
end

function write_footer(io::IO, s::SMTSolver)
    write(io, "(check-sat)\n")
    write(io, "(get-value ($(join(keys(s.vars), " "))))\n")
end

function write_footer(io::IO, s::YicesSolver)
    write(io, "(check)\n")
    write(io, "(show-model)\n")
end

function write_problem(io::IO, s::T) where {T<:NLSolver}
    write_header(io, s)
    write_vars(io, s)
    write_constraints(io, s)
    write_footer(io, s)
end

function solve(s::T; timeout::Int=-1) where {T<:NLSolver}
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
