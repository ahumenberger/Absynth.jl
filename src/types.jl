const SymOrNum = Union{Symbol,Number}

@enum MatrixShape FullSymbolic UpperTriangular UnitUpperTriangular Companion UserSpecific

_FullSymbolic(s::Int)        = [mkpoly(mkvar("b$i$j")) for i in 1:s, j in 1:s]
_UpperTriangular(s::Int)     = [j>=i ? mkpoly(mkvar("b$i$j")) : mkpoly(0) for i in 1:s, j in 1:s]
_UnitUpperTriangular(s::Int) = [j>i ? mkpoly(mkvar("b$i$j")) : i==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]
_Companion(s::Int)           = [i==s ? mkpoly(mkvar("b$i$j")) : i+1==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]
_UserSpecific(s::Int)        = error("Should not be called")

function _add_const_one(M::Matrix)
    s = size(M, 1) + 1
    col = [mkpoly(mkvar("b$i$s")) for i in 1:s-1]
    _add_row_one(hcat(M, col))
end

function _add_row_one(M::Matrix)
    T = eltype(M)
    M = vcat(M, zeros(T, 1, size(M, 2)))
    M[end,end] = one(T)
    M
end

function initmatrix(vars::Vector{Symbol}, params::Vector{SymOrNum})
    rows, cols = length(vars), length(params)
    A = fill(mkpoly(1), (rows,cols))

    for i in 1:rows, j in 1:cols
        u, v = vars[i], params[j]
        if u == v
            A[i,j] = j == findfirst(x->x==u, params) ? 1 : 0
        else
            A[i,j] = findfirst(x->x==u, params) === nothing ? mkvar("a$i$j") : 0
        end
    end
    A
end

function bodymatrix(s::Int, shape::MatrixShape)
    f = Meta.parse(string("_", shape))
    eval(:($f($s)))
end

# ------------------------------------------------------------------------------

struct RecSystem
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    init::Matrix{<:Number}
    body::Matrix{<:Number}
end

Base.size(s::RecSystem) = length(s.vars)

value(l::RecSystem, k::Int) = l.body^k * l.init
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
    init = [:($rhs = $lhs) for (rhs,lhs) in zip(rhss, l.init*map(mkpoly, l.params)) if rhs != one(Int)]
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
    shape::MatrixShape
end

function RecurrenceTemplate(vars::Vector{Symbol}, shape::MatrixShape; constone::Bool=true, params::Vector{Symbol}=Symbol[])
    size = length(vars)
    params = SymOrNum[params; 1]

    B = bodymatrix(size, shape)
    A = initmatrix(vars, params)

    if constone
        push!(vars, CONST_ONE_SYM)
        B = _add_const_one(B)
        A = _add_row_one(A)
    end
    
    RecurrenceTemplate(vars, params, B, A, shape)
end

Base.size(rt::RecurrenceTemplate) = length(rt.vars)

# ------------------------------------------------------------------------------

struct ClosedFormTemplate
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    multiplicities::Vector{Int}

    function ClosedFormTemplate(v::Vector{Symbol}, p::Vector{SymOrNum}, m::Vector{Int})
        @assert length(v) == sum(m) "The sum of multiplicites has to match the number of variables."
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
    pcp = cscforms & csinit & csroots & csrel
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

    solver = T()
    NLSat.variables!(solver, varmap)
    NLSat.constraints!(solver, pcp)
    solver
end

function parse_model(sp::SynthesisProblem, model::NLModel)
    _A, _B = init(sp), body(sp)
    A = Number[get(model, Symbol(string(b)), b) for b in _A]
    B = Number[get(model, Symbol(string(b)), b) for b in _B]
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
        cstr = constraints(cfin; split_vars=splitvars)
        :($cstr)
    end
    eval(res)
end

"Generate constraints ensuring that the root symbols are roots of the characteristic polynomial of B."
function cstr_roots(sp::SynthesisProblem)
    B, rs, ms = body(sp), roots(sp), multiplicities(sp)
    λ = mkvar(gensym_unhashed(:x))
    BB = copy(B)
    for i in diagind(B)
        BB[i] = λ - BB[i]
    end
    cpoly = det(BB)
    factors = prod((λ - r)^m for (r, m) in zip(rs,ms))
    ps = destructpoly(cpoly - factors, λ)
    cs1 = ClauseSet(map(Clause ∘ Constraint{EQ}, ps))

    ps = [r1-r2 for (r1,r2) in combinations(rs, 2)]
    cs2 = ClauseSet(map(Clause ∘ Constraint{NEQ}, ps))

    cs1 & cs2
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
    cs = B * B * A - B * A
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
    _print_recsystem(io, r.vars, r.body, init)
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