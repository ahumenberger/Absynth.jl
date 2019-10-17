
const SymOrNum = Union{Symbol,Number}

abstract type DynamicsMatrix end

FullMatrix(s::Int) = [mkpoly(mkvar("b$i$j")) for i in 1:s, j in 1:s]
UpperTriangular(s::Int) = [j>=i ? mkpoly(mkvar("b$i$j")) : mkpoly(0) for i in 1:s, j in 1:s]
UnitUpperTriangular(s::Int) = [j>i ? mkpoly(mkvar("b$i$j")) : i==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]
Companion(s::Int) = [i==s ? mkpoly(mkvar("b$i$j")) : i+1==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]

_add_const_one(M::Matrix) = _add_row_one(hcat(M, zeros(eltype(M), size(M, 1), 1)))

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

function bodymatrix(s::Int, shape::Symbol)
    if shape == :Full
        FullMatrix(s)
    elseif shape == :UpperTriangular
        UpperTriangular(s)
    elseif shape == :UnitUpperTriangular
        UnitUpperTriangular(s)
    elseif shape == :Companion
        Companion(s)
    else
        error("Unknown matrix shape: $shape")
    end
end

# ------------------------------------------------------------------------------

struct RecSystem
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    init::Matrix{<:Number}
    body::Matrix{<:Number}
end

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

function code(l::RecSystem)
    body, vars = sequentialize(l.body, l.vars)
    lhss = (Meta.parse ∘ string).(body * vars)
    init = [:($rhs = $lhs) for (rhs,lhs) in zip(l.vars, l.init*l.params)]
    assign = [:($rhs = $lhs) for (rhs,lhs) in zip(vars, lhss)]
    striplines(quote
        $(init...)
        while true
            $(assign...)
        end
    end)
end

# ------------------------------------------------------------------------------

struct RecurrenceTemplate
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    body::Matrix{<:Poly}
    init::Matrix{<:Poly}
end

function RecurrenceTemplate(vars::Vector{Symbol}; constone::Bool = false, matrix::Symbol = :Full, params::Vector{Symbol}=Symbol[])
    size = length(vars)
    params = SymOrNum[params; 1]

    B = bodymatrix(size, matrix)
    A = initmatrix(vars, params)

    if constone
        push!(vars, :cc)
        B = _add_const_one(B)
        A = _add_row_one(A)
    end
    
    RecurrenceTemplate(vars, params, B, A)
end

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
    poly = sum(coeffvec2(i, j, idx, params=params) * first(pairs[i]) * parg^(j-1) for i in 1:nroots for j in 1:ms[i])
    CFiniteExpr{lc}(poly, Dict(pairs))
end

# ------------------------------------------------------------------------------

struct SynthesisProblem
    inv::Invariant
    rt::RecurrenceTemplate
    ct::ClosedFormTemplate

    function SynthesisProblem(inv::Invariant, rt::RecurrenceTemplate, ct::ClosedFormTemplate)
        @assert issubset(program_variables(inv), rt.vars)
        @assert rt.vars == ct.vars && rt.params == ct.params
        new(inv, rt, ct)
    end
end

vars(s::SynthesisProblem) = s.rt.vars
params(s::SynthesisProblem) = s.rt.params
params(::Type{Poly}, s::SynthesisProblem) = map(mkpoly, params(s))

body(s::SynthesisProblem) = s.rt.body
init(s::SynthesisProblem) = s.rt.init

multiplicities(s::SynthesisProblem) = s.ct.multiplicities
roots(s::SynthesisProblem) = symroot(length(multiplicities(s)))

function constraints(sp::SynthesisProblem; progress::Bool=false)
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

function create_solver(sp::SynthesisProblem, T::Type{<:NLSolver}; progress::Bool=false)
    pcp = constraints(sp; progress=progress)
    vars = NLSat.variables(pcp)
    varmap = convert(Dict{Symbol,Type}, Dict(v=>AlgebraicNumber for v in vars))
    @debug "Variables" varmap

    solver = T()
    NLSat.variables!(solver, varmap)
    NLSat.constraints!(solver, pcp)
    solver
end

const NLModel = Dict{Symbol,Number}

function parse_model(sp::SynthesisProblem, model::NLModel)
    _A, _B = init(sp), body(sp)
    A = Number[get(model, Symbol(string(b)), b) for b in _A]
    B = Number[get(model, Symbol(string(b)), b) for b in _B]
    RecSystem(vars(sp), params(sp), A, B)
end

function solve(sp::SynthesisProblem; solver::Type{<:NLSolver}=Z3Solver, progress::Bool=false, timeout::Int=10)
    _solver = create_solver(sp, solver; progress=progress)
    status, elapsed, model = NLSat.solve(_solver, timeout = timeout)
    if status == NLSat.sat
        return SynthesisResult(parse_model(sp, model), elapsed, sp)
    end
    SynthResult(status, elapsed, sp)
end

"Generate constraints ensuring that p is an algebraic relation."
function cstr_algrel(sp::SynthesisProblem)
    res = constraint_walk(sp.inv) do poly
        expr = function_walk(poly) do func, args
            @assert length(args) == 1 "Invariant not properly preprocessed"
            :($(closed_form(sp.ct, sp.inv.lc, func, args[1])))
        end
        cfin = eval(expr)
        cstr = constraints(cfin; split_vars=Any[sp.ct.params; sp.inv.lc])
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
    ps = destructpoly(cstr, pars)
    ClauseSet(map(Clause ∘ Constraint{EQ}, ps))
end

"Generate constraints describing the relationship between entries of B and the closed forms."
function cstr_cforms(sp::SynthesisProblem)
    B, rs, ms = body(sp), roots(sp), multiplicities(sp)
    pars = params(Poly, sp)
    t = length(ms)
    rows = size(B, 1)
    Ds = [sum(binomial(k-1, j-1) * coeffvec(i, k, rows, params=pars) * rs[i] for k in j:ms[i]) - B * coeffvec(i, j, rows, params=pars) for i in 1:t for j in 1:ms[i]]
    ps = destructpoly(collect(Iterators.flatten(Ds)), pars)
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
        ps = destructpoly([c], pars)
        res |= Clause(map(Constraint{NEQ}, ps))
    end
    ClauseSet(res)
end

# ------------------------------------------------------------------------------

struct SynthesisResult
    result::Union{RecSystem,NLStatus}
    elapsed::TimePeriod
    problem::SynthesisProblem
end

# ------------------------------------------------------------------------------

function Base.summary(io::IO, rt::RecurrenceTemplate)
    compact = get(io, :compact, false)
    if compact
        print(io, "RecurrenceTemplate ($(size(rt.body, 1)))")
    else
        print(io, "RecurrenceTemplate of size $(size(rt.body, 1))")
    end
end

function Base.show(io::IO, ::MIME"text/plain", rt::Union{RecurrenceTemplate,RecSystem})
    summary(io, rt)
    println(io, ":")
    init = rt.init * map(mkpoly, rt.params)
    _print_recsystem(io, rt.vars, rt.body, init)
end