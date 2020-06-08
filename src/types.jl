
init_var(s::Symbol) = Symbol(string(s, "00"))

struct RecSystem
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    init::Matrix{<:Number}
    body::Matrix{<:Number}
end

Base.size(s::RecSystem) = length(s.vars)

function value(l::RecSystem, k::Int)
    @assert k >= 0
    iszero(k) && return tuple(l.init...)
    tuple((l.body^k * l.init)...)
end

value(l::RecSystem, r::UnitRange{Int}) = [value(l, k) for k in r]

function sequentialize(M::Matrix, v::Vector)
    LinearAlgebra.istriu(M) && return M, v
    h = size(M, 2)
    V = [mkvar("_" * string(x)) for x in v]
    V = [V; v]
    tl = zeros(Int, h, h)
    tr = UniformScaling(1)
    bl = LowerTriangular(M) - Diagonal(M)
    br = M - bl
    B = vcat(hcat(tl, tr), hcat(bl, br))
    zcols = findall(iszero, collect(eachcol(B)))
    B[setdiff(1:end, zcols), setdiff(1:end, zcols)], V[setdiff(1:end, zcols)]
end

function loop(l::RecSystem)
    body, vars = sequentialize(l.body, map(mkvar, l.vars))
    lhss = (Meta.parse ∘ string).(body * vars)
    lhss = [replace(x, CONST_ONE_SYM, one(Int)) for x in lhss]
    rhss = [replace(x, CONST_ONE_SYM, one(Int)) for x in l.vars]
    pars = map(x->(x isa Symbol ? mkpoly(init_var(x)) : mkpoly(x)), l.params)
    init = [:($rhs = $lhs) for (rhs,lhs) in zip(rhss, l.init*pars) if rhs != one(Int)]
    assign = [:($rhs = $lhs) for (rhs,lhs) in zip(rhss, lhss) if rhs != lhs]
    striplines(quote
        $(init...)
        while true
            $(assign...)
        end
    end)
end

# ------------------------------------------------------------------------------

const CONST_ONE_SYM = :_c
const ROOT_SYM = :_w

struct RecurrenceTemplate
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    body::Matrix{<:Poly}
    init::Matrix{<:Poly}
end

RecurrenceTemplate(r::RecTemplate, vars::Vector{Symbol}) =
    RecurrenceTemplate(vars, r.params, r.body, r.init)

Base.size(rt::RecurrenceTemplate) = length(rt.vars)

variables_init(r::RecurrenceTemplate) =
    [Symbol(string(v)) for v in r.init if !isconstant(v)]

variables_body(r::RecurrenceTemplate) =
    [Symbol(string(v)) for v in r.body if !isconstant(v)]

# ------------------------------------------------------------------------------

struct ClosedFormTemplate
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    multiplicities::Vector{Int}

    function ClosedFormTemplate(v::Vector{Symbol}, p::Vector{SymOrNum}, m::Vector{Int})
        @assert length(v) == sum(m) "The sum of multiplicites has to match the number of variables. Got $(sum(m)), need $(length(v))"
        new(v, p, m)
    end
end

ClosedFormTemplate(rt::RecurrenceTemplate, ms::Vector{Int}) = ClosedFormTemplate(rt.vars, rt.params, ms)

function closed_form(ct::ClosedFormTemplate, lc::Symbol, var::Symbol, arg)
    ms = ct.multiplicities
    rs = symroot(length(ms))
    idx = findfirst(x->x==var, ct.vars)
    nroots = length(rs)
    parg = mkpoly(arg)
    pairs = [replacement_pair(NExp{lc}(rs[i], parg)) for i in 1:nroots]
    params = map(mkpoly, ct.params)
    poly = sum(coeff_var(i, j, idx, params=params) * first(pairs[i]) * parg^(j-1) for i in 1:nroots for j in 1:ms[i])
    CFiniteExpr{lc}(poly, Dict(pairs))
end

# ------------------------------------------------------------------------------

coeff_vec(i::Int, j::Int, rows::Int; params::Vector{<:Poly}) =
    [coeff_var(i, j, k, params=params) for k in 1:rows]

coeff_var(i::Int, j::Int, varidx::Int; params::Vector{<:Poly}) =
    sum(mkvar("c$i$j$(varidx)$l") * p for (l,p) in enumerate(params))

symroot(n::Int) = [mkvar(string(ROOT_SYM, i)) for i in 1:n]

cforms(varcnt::Int, rs::Vector{<:Var}, ms::Vector{Int}; lc::Union{Int,Var}, exp::Int, params::Vector{<:Poly}) =
    sum(coeff_vec(i, j, varcnt, params=params) * rs[i]^exp * lc^(j-1) for i in 1:length(rs) for j in 1:ms[i])

# ------------------------------------------------------------------------------

struct SynthesisProblem
    inv::Invariant
    rt::RecurrenceTemplate
    ct::ClosedFormTemplate

    function SynthesisProblem(inv::Invariant, rt::RecurrenceTemplate, ct::ClosedFormTemplate)
        @assert issubset(program_variables(inv), rt.vars) "$(program_variables(inv)) is not a subset of $(rt.vars)"
        @assert rt.vars == ct.vars && rt.params == ct.params
        new(inv, rt, ct)
    end
end

vars(s::SynthesisProblem) = s.rt.vars
params(s::SynthesisProblem) = s.rt.params
params(::Type{Poly}, s::SynthesisProblem) = map(mkpoly, params(s))
params(::Type{Symbol}, s::SynthesisProblem) = filter(x->x isa Symbol, params(s))
params(::Type{Var}, s::SynthesisProblem) = map(mkvar, params(Symbol, s))

body(s::SynthesisProblem) = s.rt.body
init(s::SynthesisProblem) = s.rt.init

multiplicities(s::SynthesisProblem) = s.ct.multiplicities
roots(s::SynthesisProblem) = symroot(length(multiplicities(s)))

function constraints(sp::SynthesisProblem; progress::Bool=true)
    cscforms = cstr_cforms(sp)
    csinit   = cstr_init(sp)
    csroots  = cstr_roots(sp)
    csrel    = cstr_algrel(sp)
    @debug "Constraints" cscforms csinit csroots csrel
    pcp = csroots & cscforms & csinit & csrel
    if progress
        pcp &= cstr_progress(sp)
    end
    pcp
end

function create_solver(sp::SynthesisProblem, T::Type{<:NLSolver}; progress::Bool=true)
    pcp = constraints(sp; progress=progress)
    vars = NLSat.variables(pcp)
    varmap = convert(Dict{Symbol,Type}, Dict(v=>AlgebraicNumber for v in vars))
    @debug "Variables" varmap

    vs = variables_body(sp.rt)
    soft = ClauseSet([Clause(Constraint{EQ}(v)) for v in vs])

    solver = T()
    NLSat.add_vars!(solver, varmap)
    NLSat.add!(solver, pcp)
    # NLSat.add_soft!(solver, soft)
    solver
end

function parse_model(sp::SynthesisProblem, model::Dict{Symbol,T}) where {T<:Number}
    _A, _B = init(sp), body(sp)
    A = T[get(model, Symbol(string(b)), b) for b in _A]
    B = T[get(model, Symbol(string(b)), b) for b in _B]
    RecSystem(vars(sp), params(sp), A, B)
end

function solve(sp::SynthesisProblem, solver::S; timeout::Int) where {S<:NLSolver}
    status, elapsed, model = NLSat.solve(solver, timeout = timeout)
    @debug "Solver result" status model
    if status == NLSat.sat
        return model, SynthesisResult(status, parse_model(sp, model), elapsed, sp)
    end
    nothing, SynthesisResult(status, nothing, elapsed, sp)
end

function solve(sp::SynthesisProblem; solver::Type{<:NLSolver}=Z3Solver, progress::Bool=true, timeout::Int=10)
    _solver = create_solver(sp, solver; progress=progress)
    last(solve(sp, _solver, timeout=timeout))
end

"Generate constraints ensuring that p is an algebraic relation."
function cstr_algrel(sp::SynthesisProblem)
    res = constraint_walk(sp.inv) do poly
        expr = function_walk(poly) do func, args
            @assert length(args) == 1 "Invariant not properly preprocessed"
            :($(closed_form(sp.ct, sp.inv.lc, func, args[1])))
        end
        cfin = eval(expr)
        splitvars = Symbol[params(Symbol, sp); sp.inv.lc]
        cstr = cfinite_constraints(cfin; split_vars=splitvars)
        :($cstr)
    end
    eval(res)
end

"Generate constraints ensuring that the root symbols are roots of the characteristic polynomial of B."
function cstr_roots(sp::SynthesisProblem)
    B, rs, ms = body(sp), roots(sp), multiplicities(sp)
    λ = mkvar(gensym_unhashed(:x))
    BB = -B
    for i in diagind(B)
        BB[i] = λ + BB[i]
    end
    cpoly = det(BB)
    factors = prod((λ - r)^m for (r, m) in zip(rs,ms))
    ps = destructpoly(cpoly - factors, λ)
    cs1 = ClauseSet(map(Clause ∘ Constraint{EQ}, ps))

    ps = [r1-r2 for (r1,r2) in combinations(rs, 2)]
    cs2 = ClauseSet(map(Clause ∘ Constraint{NEQ}, ps))

    cs3 = ClauseSet([Clause(Constraint{NEQ}(r)) for r in rs])

    cs1 & cs2 & cs3
end

"Generate constraints defining the initial values."
function cstr_init(sp::SynthesisProblem)
    B, rs, ms = body(sp), roots(sp), multiplicities(sp)
    pars = params(Poly, sp)
    s = size(B, 1)
    d = sum(ms)
    A = init(sp) * pars
    cstr = Poly[]
    for i in 0:d-1
        M = cforms(s, rs, ms, lc=i, exp=i, params=pars)
        X = iszero(i) ? A : B^i*A
        append!(cstr, X - M)
    end
    ps = destructpoly(cstr, params(Var, sp))
    ClauseSet(map(Clause ∘ Constraint{EQ}, ps))
end

"Generate constraints describing the relationship between entries of B and the closed forms."
function cstr_cforms(sp::SynthesisProblem)
    B, rs, ms = body(sp), roots(sp), multiplicities(sp)
    pars = params(Poly, sp)
    t = length(ms)
    rows = size(B, 1)
    Ds = [sum(binomial(k-1, j-1) * coeff_vec(i, k, rows, params=pars) * rs[i] for k in j:ms[i]) - B * coeff_vec(i, j, rows, params=pars) for i in 1:t for j in 1:ms[i]]
    ps = destructpoly(collect(Iterators.flatten(Ds)), params(Var, sp))
    ClauseSet(map(Clause ∘ Constraint{EQ}, ps))
end

"Generate constraints ensuring that sequence is not constant, i.e. B*B*x0 != B*x0."
function cstr_progress(sp::SynthesisProblem)
    pars = params(Poly, sp)
    A, B = init(sp)*pars, body(sp)
    cs1 = B * B * A - B * A
    cs2 = B * B * B * A - B * A
    _cstr_progress(sp, cs1, pars) & _cstr_progress(sp, cs2, pars)
end

function _cstr_progress(sp::SynthesisProblem, cs, pars)
    # do not consider variables which only occurr as initial variable in polys
    invvars = program_variables(sp.inv)
    # filter!(!isinitvar, vars)
    nonloopvars = setdiff(vars(sp), invvars)
    inds = [i for (i, v) in enumerate(vars(sp)) if !(v in invvars)]
    deleteat!(cs, inds)
    res = Clause()
    for c in cs
        ps = destructpoly([c], params(Var, sp))
        res |= Clause(map(Constraint{NEQ}, ps))
    end
    ClauseSet(res)
end

# ------------------------------------------------------------------------------

struct SynthesisResult
    status::NLStatus
    recsystem::Union{RecSystem,Nothing}
    elapsed::TimePeriod
    problem::SynthesisProblem
end

issat(s::SynthesisResult) = s.status == NLSat.sat

# ------------------------------------------------------------------------------

function Base.summary(io::IO, r::Union{RecurrenceTemplate,RecSystem})
    compact = get(io, :compact, false)
    if compact
        print(io, "$(typeof(r)) ($(size(r)))")
    else
        print(io, "$(typeof(r)) of size $(size(r))")
    end
end

function Base.show(io::IO, r::Union{RecurrenceTemplate,RecSystem})
    summary(io, r)
    compact = get(io, :compact, false)
    if !compact
        println(io, ":")
        _show(io, r)
    end
end

function _show(io::IO, r::Union{RecurrenceTemplate,RecSystem})
    init = r.init * map(mkpoly, r.params)
    vars = [v == CONST_ONE_SYM ? "1" : "$v" for v in r.vars]
    _print_recsystem(io, vars, r.body, init)
end

function Base.show(io::IO, s::SynthesisResult)
    compact = get(io, :compact, false)
    if compact
        print(io, "SynthesisResult($(s.status), $(s.elapsed))")
    else
        print(io, "SynthesisResult ($(s.status)) in $(s.elapsed)")
        if !isnothing(s.recsystem)
            println(io)
            _show(io, s.recsystem)
        end
    end
end