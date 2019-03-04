module Absynth

include("nlsat.jl")

using MacroTools
using Absynth.NLSat
using SymEngine
using Recurrences

export LoopTemplate, loop
export Synthesizer, solve, constraints!, invariants!

# ------------------------------------------------------------------------------

atoms(f, ex) = MacroTools.postwalk(x -> x isa Symbol && Base.isidentifier(x) ? f(x) : x, ex)
function free_symbols(ex::Expr)
    ls = Symbol[]
    atoms(x -> (push!(ls, x); x), ex)
    Base.unique(ls)
end

function clear_denom(f::Basic)
    ls = Recurrences.summands(f) |> Iterators.flatten
    ds = denom.(ls)
    val = Recurrences.lcm2(ds...)
    f*val
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
        vset = union(keys(args), vars)
        left = setdiff(fsyms, vset)
        @assert isempty(left) "Neither loop variables nor unknowns: $left"

        notneeded = setdiff(keys(args), fsyms)
        if !isempty(notneeded)
            for v in notneeded
                delete!(args, v)
            end
            @warn "Too many unknowns specified: $(join(notneeded, ","))"
        end

        new(name, args, body, vars, [])
    end
end

name(t::LoopTemplate) = t.name
args(t::LoopTemplate) = t.args
vars(t::LoopTemplate) = t.vars
body(t::LoopTemplate) = t.body

function (t::LoopTemplate)(vals::Union{Int,Rational}...)
    @assert length(vals) <= length(t.args) "Too many arguments"
    body = t.body
    vars = collect(keys(t.args))
    for (i, v) in enumerate(vals)
        body = [MacroTools.replace(x, vars[i], v) for x in body]
    end
    LoopTemplate(t.name, Dict(collect(t.args)[length(vals)+1:end]), body)
end

function initvalues!(t::LoopTemplate, v::Vector{IntOrRat})
    # TODO: figure out how to handle initial values
    append!(t.ivals, v)
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

    entries = Recurrences.LinearEntry{Basic}[]    
    for (lhs, rhs) in zip(lhss, rhss)
        expr = Expr(:call, :-, lhs, rhs)
        entry, _ = Recurrences.LinearRecEntry(Basic, expr)
        push!(entries, entry)
    end

    sys = LinearRecSystem(Basic(lc))
    push!(sys, entries...)
    @debug "Rec system" sys
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

mutable struct Synthesizer
    tmpl::LoopTemplate
    invs::Vector{Expr}
    cstr::Vector{Expr}      # user-defined constraints
    invcstr::Vector{Expr}   # constraints induced by invariants
    updated::Bool           # indicates whether constraints have to be recomputed
end

Synthesizer(tmpl::LoopTemplate) = Synthesizer(tmpl, Expr[], Expr[], Expr[], true)
Synthesizer(tmpl::LoopTemplate, invs::Expr...) = Synthesizer(tmpl, invs, Expr[], Expr[], true)

template(s::Synthesizer) = s.tmpl
constraints(s::Synthesizer) = s.cstr
invariants(s::Synthesizer) = s.invs
invconstraints(s::Synthesizer) = s.invcstr

isconstraint(c::Expr) = c.head == :call && c.args[1] in [:(==), :(<=), :(>=), :(<), :(>), :(!=)]

function constraints!(s::Synthesizer, cstr::Expr...)
    for c in cstr
        if isconstraint(c)
            push!(s.cstr, c)
        else
            @error "Only equalities and inequalties allowed. Ignoring $c"
        end
    end
end

function invariants!(s::Synthesizer, invs::Expr...)
    for c in invs
        if @capture(c, lhs_ == rhs_)
            s.updated = true
            push!(s.invs, c)
        else
            @error "Only equalities and inequalties allowed. Ignoring $c"
        end
    end
end

function _constraints!(s::Synthesizer)
    sys = lrs(template(s))
    cforms = Recurrences.solve(sys)

    ivars = Dict(Recurrences.initvariable(f, 0) => f for f in sys.funcs)

    @debug "Closed forms" cforms
    d = [cf.func => expression(cf) for cf in cforms]
    @debug "Replacement dicitonary" d

    for invariant in invariants(s)
        @capture(invariant, lhs_ == rhs_)
        expr = Basic(lhs) - Basic(rhs)
        expr = subs(expr, d...)
        expr = subs(expr, ivars...)
        expr = expand(expr * denominator(expr))

        cfs = Recurrences.coeffs(expr, sys.arg)
        @debug "Coefficients from invariant" cfs

        cstr = [Expr(:call, :(==), 0, convert(Expr, c)) for c in cfs]

        push!(s.invcstr, cstr...)
    end
    s.updated = false
end

function solve(s::Synthesizer, ::Type{T} = Z3Solver) where {T<:NLSolver}
    @assert !isempty(invariants(s)) "No invariants specified."
    if s.updated
        _constraints!(s)
    end

    solver = T()
    # use promoted type for loop variables
    @debug "Types for unknowns" types = args(template(s))
    t = promote_type(values(args(template(s)))...)
    vs = Dict{Symbol,Type}(map(x -> x=>t, vars(template(s))))
    @debug "Promotion types for loop variables" types = vs
    NLSat.variables!(solver, args(template(s))..., vs...)
    if !isempty(constraints(s))
        NLSat.constraints!(solver, constraints(s)...)
    end
    if !isempty(invconstraints(s))
        NLSat.constraints!(solver, invconstraints(s)...)
    end

    status, model = NLSat.solve(solver)
    @debug "Result of $T" status model
    if status == NLSat.sat
        lt = template(s)
        undef = setdiff(keys(args(lt)), keys(model))
        if !isempty(undef)
            # TODO: deal with unknowns which do not appear in model
            for v in undef
                push!(model, v => 0)
            end
        end
        lt([model[v] for v in keys(args(lt))]...)
    else
        @error "No solution exists. Result of $T: $status"
    end
end

# ------------------------------------------------------------------------------

# function test()
#     @template freire(a, b) = begin
#         x = x + a
#         y = y + b
#     end
    
#     s = Synthesizer(freire, :(x - y == 0))
#     constraint!(s, :(b > 0))
#     solve(s)
# end

include("show.jl")
include("macro.jl")

end # module
