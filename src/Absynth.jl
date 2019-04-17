module Absynth

include("nlsat.jl")

using MacroTools
using Absynth.NLSat
using SymEngine
using Recurrences

export LoopTemplate, setvalues, setvalues!
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
CoeffType = Union{Symbol,Int,Rational}

struct LoopTemplate
    name::Symbol                    # template name
    args::Dict{Symbol,Type}         # unknowns in loop body
    vars::Dict{Symbol,Type}         # loop variables
    body::Vector{Expr}              # loop body
    init::Vector{Expr}              # assignments before loop
    avals::Dict{Symbol,CoeffType}   # values for arguments
    ivals::Dict{Symbol,CoeffType}   # initial values for loop variables
    cforms::Vector{Recurrences.ClosedForm}     # closed form solutions

    function LoopTemplate(name::Symbol, args::Dict{Symbol,Type}, body::Vector{Expr})
        @assert !isempty(args) "No unknowns specified"
        @assert !isempty(body) "Template is empty"
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

        # use promoted type for loop variables
        ptype = promote_type(values(args)...)
        vars = Dict{Symbol,Type}(map(x -> x=>ptype, vars))
        @debug "Type maps" args vars

        avals = Dict(x=>x for x in keys(args))
        ivals = Dict(Symbol(Recurrences.initvar(x))=>Symbol(Recurrences.initvar(x)) for x in keys(vars))
        @debug "Value maps" avals ivals

        init = [Expr(:call, :(=), v, Symbol(Recurrences.initvar(v))) for v in keys(vars)]
        @debug "Code" body init

        sys = _lrs(body)
        cforms = Recurrences.solve(sys)
        @debug "Closed forms" cforms

        new(name, args, vars, body, init, avals, ivals, cforms)
    end

    LoopTemplate(t::LoopTemplate) = new(t.name, copy(t.args), copy(t.vars), copy(t.body), copy(t.init), copy(t.avals), copy(t.ivals), copy(t.cforms))
end

name(t::LoopTemplate) = t.name
args(t::LoopTemplate) = keys(t.args)
argmap(t::LoopTemplate) = t.args
vars(t::LoopTemplate) = keys(t.vars)
varmap(t::LoopTemplate) = t.vars
bodyexpr(t::LoopTemplate) = t.body
initexpr(t::LoopTemplate) = t.init
argvalues(t::LoopTemplate) = t.avals
initvalues(t::LoopTemplate) = t.ivals
closedforms(t::LoopTemplate) = t.cforms

Base.copy(t::LoopTemplate) = LoopTemplate(t)

function setvalues!(t::LoopTemplate, d::Dict{Symbol,T}) where {T<:CoeffType}
    for k in args(t)
        if haskey(d, k)
            t.avals[k] = d[k]
        end
    end
    for k in keys(initvalues(t))
        if haskey(d, k)
            t.ivals[k] = d[k]
        end
    end
    t
end
setvalues!(t::LoopTemplate, d::Pair...) = setvalues!(t, Dict(d))

setvalues(t::LoopTemplate, d::Dict) = setvalues!(copy(t), d)
setvalues(t::LoopTemplate, d::Pair...) = setvalues(t, Dict(d))

# function (t::LoopTemplate)(vals::Union{Int,Rational}...)
#     @assert length(vals) <= length(t.args) "Too many arguments"
#     body = t.body
#     vars = collect(keys(t.args))
#     for (i, v) in enumerate(vals)
#         body = [MacroTools.replace(x, vars[i], v) for x in body]
#     end
#     LoopTemplate(t.name, Dict(collect(t.args)[length(vals)+1:end]), body)
# end

replace_post(ex, s, s′) = MacroTools.postwalk(x -> x == s ? s′ : x, ex)

function _lrs(body::Vector{Expr})
    lhss = Symbol[]
    rhss = Expr[]
    for assign in body
        @capture(assign, lhs_ = rhs_)
        push!(lhss, lhs)
        push!(rhss, rhs isa Symbol ? Expr(:call, :*, rhs, 1) : unblock(rhs))
    end

    lc = :nn
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
            $(bodyexpr(t)...)
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
    cforms = closedforms(template(s))
    d = [cf.func => expression(cf) for cf in cforms]

    # We can assume cforms is not empty, otherwise the loop template would not exist
    lc = cforms[1].arg
    for invariant in invariants(s)
        @capture(invariant, lhs_ == rhs_)
        expr = Basic(lhs) - Basic(rhs)
        expr = subs(expr, d...)
        # expr = subs(expr, ivars...)
        expr = expand(expr * denominator(expr))

        cfs = Recurrences.coeffs(expr, lc)
        @debug "Coefficients from invariant" cfs
        filter!(x -> !iszero(x), cfs)
        @debug "Coefficients from invariant" cfs
        cstr = [Expr(:call, :(==), 0, convert(Expr, c)) for c in cfs]

        push!(s.invcstr, cstr...)
    end
    s.updated = false
end

function solve(s::Synthesizer; solver::Type{T}=Z3Solver, timeout::Int=120) where {T<:NLSolver}
    @assert !isempty(invariants(s)) "No invariants specified."
    if s.updated
        _constraints!(s)
    end

    solver = T()

    tmpl = template(s)
    ivars = Dict{Symbol,Type}(Symbol(Recurrences.initvar(k))=>v for (k,v) in varmap(tmpl))
    NLSat.variables!(solver, argmap(tmpl)..., ivars...)
    if !isempty(constraints(s))
        NLSat.constraints!(solver, constraints(s)...)
    end
    if !isempty(invconstraints(s))
        NLSat.constraints!(solver, invconstraints(s)...)
    end

    status, model = NLSat.solve(solver, timeout=timeout)
    @debug "Result of $T" status model
    if status == NLSat.sat
        undef = setdiff(args(tmpl), keys(model))
        if !isempty(undef)
            # TODO: deal with unknowns which do not appear in model
            for v in undef
                push!(model, v => 0)
            end
        end
        return setvalues(tmpl, Dict{Symbol,CoeffType}(model))
    elseif status == NLSat.timeout
        @error "Timeout"
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
