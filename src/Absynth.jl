module Absynth

include("nlsat.jl")

using MacroTools
using Absynth.NLSat
using SymEngine
using Recurrences

export @template, LoopTemplate, loop

# ------------------------------------------------------------------------------

atoms(f, ex) = MacroTools.postwalk(x -> x isa Symbol && Base.isidentifier(x) ? f(x) : x, ex)
function free_symbols(ex::Expr)
    ls = Symbol[]
    atoms(x -> (push!(ls, x); x), ex)
    Base.unique(ls)
end


IntOrRat = Union{Int,Rational}

struct LoopTemplate
    name::Symbol
    args::Dict{Symbol,Type}
    body::Vector{Expr}
    vars::Vector{Symbol}
    ivals::Vector{IntOrRat}

    function LoopTemplate(name::Symbol, args::Dict{Symbol,Type}, body::Vector{Expr})
        vars = Symbol[]
        for assign in body
            valid = @capture(assign, lhs_Symbol = rhs_) && Base.isidentifier(lhs)
            @assert valid "Not a valid assignment: $assign"
            push!(vars, lhs)
        end

        fsyms = Iterators.flatten(free_symbols.(body))
        left = setdiff(fsyms, union(keys(args), vars))
        @assert isempty(left) "Neither loop variables nor unknowns: $left"

        new(name, args, body, vars, [])
    end
end

name(t::LoopTemplate) = t.name
args(t::LoopTemplate) = t.args
vars(t::LoopTemplate) = t.vars
body(t::LoopTemplate) = t.body

function (t::LoopTemplate)(vals::Union{Int,Rational}...; ivals::Pair{Symbol,IntOrRat}...)
    @assert length(vals) <= length(t.args) "Too many arguments"
    body = t.body
    for (i, v) in enumerate(vals)
        body = [MacroTools.replace(x, t.args[i], v) for x in body]
    end
    LoopTemplate(t.name, t.args[length(vals)+1:end], body)
end

replace_post(ex, s, s′) = MacroTools.postwalk(x -> x == s ? s′ : x, ex)

function lrs(t::LoopTemplate)
    lhss = Symbol[]
    rhss = Expr[]
    for assign in body(t)
        @capture(assign, lhs_ = rhs_)
        push!(lhss, lhs)
        push!(rhss, unblock(rhs))
    end

    lc = :n
    for (i, v) in enumerate(lhss)
        rhss = [replace_post(x, v, (i < j ? Expr(:call, v, Expr(:call, :+, lc, 1)) : Expr(:call, v, lc))) for (j, x) in enumerate(rhss)]
    end

    lhss = [Expr(:call, v, Expr(:call, :+, lc, 1)) for v in lhss]

    @info "" lhss rhss

    entries = Recurrences.LinearEntry{Basic}[]    
    for (lhs, rhs) in zip(lhss, rhss)
        expr = Expr(:call, :-, lhs, rhs)
        entry, _ = Recurrences.LinearRecEntry(Basic, expr)
        push!(entries, entry)
    end

    sys = LinearRecSystem(Basic(lc))
    push!(sys, entries...)
    @info "" sys
    sys
end

function loop(t::LoopTemplate; iterations::Int = 10)
    quote
        for _ in 1:$iterations
            $(t.body...)
        end
    end
end

# ------------------------------------------------------------------------------

struct Synthesizer{T<:NLSolver}
    tmpl::LoopTemplate
    inv::Expr
    cstr::Vector{Expr}
end

Synthesizer{T}(tmpl::LoopTemplate, inv::Expr) where {T} = Synthesizer{T}(tmpl, inv, Expr[])
Synthesizer(args...) = Synthesizer{Z3Solver}(args...)

template(s::Synthesizer) = s.tmpl
constraints(s::Synthesizer) = s.cstr

function constraints!(s::Synthesizer, cstr::Expr...)
    push!(s.cstr, cstr...)
end

function _constraints!(s::Synthesizer)
    sys = lrs(template(s))
    cforms = Recurrences.solve(sys)

    expr = expression.(cforms)
    @info "" expr convert.(Expr, expr)
end

function solve(s::Synthesizer{T}) where {T}
    solver = T()
    # use promoted type for loop variables
    @info "" values(args(template(s)))
    t = promote_type(values(args(template(s)))...)
    vs = Dict{Symbol,Type}(map(x -> x=>t, vars(template(s))))
    @info "" vs
    variables!(solver, args(template(s))..., vs...)
    if !isempty(constraints(s))
        constraints!(solver, constraints(s)...)
    end
    _constraints!(s)

    # status, model = solve(solver)
    # @info "Synthesis" status model
end

# ------------------------------------------------------------------------------

macro template(input)

    @capture(input, name_(args__) = begin assignments__ end)

    tname = [name]

    @info "" tname args assignments

    args = Dict{Any,Any}(map(x -> MacroTools.splitarg(x)[1:2], args))
    # set default variable type to Rational
    replace!(args) do kv
        println(last(kv) == :Any)
        last(kv) == :Any ? first(kv) => Rational{Int} : first(kv) => eval(last(kv))
    end
    args = convert(Dict{Symbol,Type}, args)

    return esc(:($name = LoopTemplate($(tname)..., $(args), convert(Vector{Expr}, $(assignments)))))
end

function test()
    @template freire(a, b) = begin
        x = x + a
        y = y + b
    end
    
    s = Synthesizer(freire, :(x - y == 0))
    constraint!(s, :(b > 0))
    synth(s)
end

end # module
