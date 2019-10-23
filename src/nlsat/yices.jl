prefix(x::Symbol) = string(x)
function prefix(x::Expr)
    s = sprint(Meta.show_sexpr, x)
    s = Base.replace(s, ":call, " => "")
    s = Base.replace(s, ":" => "")
    s = Base.replace(s, "," => "")
    s = Base.replace(s, "(==)" => "=")
    s = Base.replace(s, "!=" => "distinct")
    s = Base.replace(s, "||" => "or")
    s = Base.replace(s, "//" => "/")
    s
end

prefix(c::Constraint{EQ}) = string("(= ", prefix(c.poly), " 0)")
prefix(c::Constraint{NEQ}) = string("(distinct ", prefix(c.poly), " 0)")

prefix(c::Clause) = length(c) == 1 ? prefix(first(c)) : string("(or ", join([prefix(x) for x in c], " "), ")")

mutable struct YicesSolver <: NLSolver
    vars::Dict{Symbol,Type}
    cs::ClauseSet
    pyvars::Dict{Symbol, PyObject}
    cstr::Vector{PyObject}
    input::Vector{String}
    function YicesSolver()
        @assert !isnothing(Sys.which("yices")) "Could not find Yices"
        init_yices()
        @assert !ispynull(yices) "Could not install Python interface of Yices"
        new(Dict(), ClauseSet(), Dict(), [], [])
    end
end

function variables!(s::YicesSolver, d::Dict{Symbol,Type})
    for (v,t) in d
        pyvar = yices.Terms.new_uninterpreted_term(yices_typemap[t], string(v))
        push!(s.pyvars, v=>pyvar)
        push!(s.vars, v=>t)
    end
end

function solve(s::YicesSolver; timeout::Int = -1)
    cfg = yices.Config()
    cfg.default_config_for_logic("QF_NRA")
    ctx = yices.Context(cfg)

    for c in s.cs
        prefix_str = prefix(c)
        term = yices.Terms.parse_term(prefix_str)
        # push!(s.cstr, term)
        push!(s.input, yices.Terms.to_string(term, 200))
    end
    # ctx.assert_formulas(s.cstr)

    mktemp() do path, io
        write_yices(io, s)
        openproc(`yices --logic=QF_NRA $path`, timeout=timeout) do lines
            d = Dict{Symbol,Number}()
            for l in lines
                ll = l[4:end-1]
                (x,y) = split(ll, limit=2)
                sym = Symbol(x)
                val = parsenumber(y)
                push!(d, sym=>val)
            end
            d
        end
    end
end

function write_yices(io::IO, s::YicesSolver)
    for v in keys(s.vars)
        write(io, "(define $v::real)\n")
    end
    for x in s.input
        write(io, "(assert $x)\n")
    end
    write(io, "(check)\n")
    write(io, "(show-model)\n")
    close(io)
end

function parsenumber(s::AbstractString)
    T = Int
    ls = split(string(s), '/', keepempty=false)
    if length(ls) == 1
        return parse(T, ls[1])
    else
        @assert length(ls) == 2
        return parse(T, ls[1]) // parse(T, ls[2])
    end
end