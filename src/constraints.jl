@enum MatrixShape full upper uni

function dynamicsmatrix(size::Int, shape::MatrixShape)
    if shape == full
        # full
        B = Poly[mkvar("b$i$j") for i in 1:size, j in 1:size]
    elseif shape == upper
        # upper triangular
        B = Poly[j>=i ? mkvar("b$i$j") : mkpoly(0) for i in 1:size, j in 1:size]
    elseif shape == uni
        # unitriangular
        B = Poly[j>i ? mkvar("b$i$j") : i==j ? mkpoly(1) : mkpoly(0) for i in 1:size, j in 1:size]
    end
    B
end

initvar(s::T) where {T<:Union{Symbol,Var}} = T("$(string(s))00")
isinitvar(s::Union{Symbol,Var}) = endswith(string(s), "00")
basevar(s::Union{Symbol,Var}) = isinitvar(s) ? mkvar(string(s)[1:end-2]) : s

function filtervars(fs)
    init = filter(isinitvar, fs)
    init, unique(map(basevar, fs))
end

# ------------------------------------------------------------------------------

# to_expr(xs::Vector{Basic}) = map(x->convert(Expr, x), xs)

eq(x::Poly, y::Int=zero(Int)) = Expr(:call, :(==), Meta.parse(string(x)), Meta.parse(string(y)))
ineq(x::Poly, y::Int=zero(Int)) = Expr(:call, :(!=), Meta.parse(string(x)), Meta.parse(string(y)))
function or(xs::Expr...)
    if length(xs) == 1
        return xs[1]
    elseif length(xs) == 2
        return Expr(:(||), xs[1], xs[2])
    end
    return Expr(:(||), xs[1], or(xs[2:end]...))
end

gensym_unhashed(s::Symbol) = Symbol(Base.replace(string(gensym(s)), "#"=>""))

# ------------------------------------------------------------------------------

struct SynthContext
    inv::Invariant
    vars::Vector{<:Var}
    params::Vector{<:Poly}
    roots::Vector{<:Var}
    multi::Vector{Int}
    body::Matrix{<:Poly}
    init::Matrix{<:Poly}
    lc::Var
end

function mkcontext(body::Matrix{<:Poly}, init::Matrix{<:Poly}, inv::Invariant, vars::Vector{<:Var}, params::Vector{<:Var}, ms::Vector{Int})
    rs, lc = symroot(length(ms)), mkvar(inv.lc)
    SynthContext(inv, vars, [params; mkpoly(1)], rs, ms, body, init, lc)
end

# ------------------------------------------------------------------------------

function raw_constraints(ctx::SynthContext)
    # Equality constraints
    cscforms = cstr_cforms(ctx)
    csinit   = cstr_init(ctx)
    csroots  = cstr_roots(ctx)
    csrel    = cstr_algrel(ctx)
    @debug "Equality constraints" cscforms csinit csroots csrel
    # Inequality constraints
    csdistinct = cstr_distinct(ctx)
    @debug "Inequality constraints" csdistinct
    pcp = cscforms & csinit & csroots & csrel & csdistinct

    vars = NLSat.variables(pcp)
    varmap = convert(Dict{Symbol,Type}, Dict(v=>AlgebraicNumber for v in vars))
    @debug "Variables" varmap

    varmap, pcp
end

function constraints(ctx::SynthContext)
    raw_constraints(ctx)
    # varmap, [map(eq, equalities); map(ineq, inequalities)]
end

function constraints_opt(ctx::SynthContext)
    ps = cstr_nonconstant(ctx)
    ClauseSet(map(Clause ∘ Constraint{NEQ}, ps))
end

# ------------------------------------------------------------------------------

function cforms(varcnt::Int, rs::Vector{<:Var}, ms::Vector{Int}; lc::Union{Int,Var}, exp::Int, params::Vector{<:Poly})
    t = length(rs)
    sum(coeffvec(i, j, varcnt, params=params) * rs[i]^exp * lc^(j-1) for i in 1:t for j in 1:ms[i])
end

function coeffvec(i::Int, j::Int, rows::Int; params::Vector{<:Poly})
    nparams = length(params)

    # s = collect('c':'z')[i*j]
    # C = [Basic("$s$k$l") for k in 1:rows, l in 1:nparams]
    C = [mkvar("c$i$j$k$l") for k in 1:rows, l in 1:nparams]
    C * params
end

function initvec(vars::Vector{<:Var}, params::Vector{<:Var})
    rows, cols = length(vars), length(params)+1
    baseparams = [map(basevar, params); 1]
    A = fill(mkpoly(1), (rows,cols))

    for i in 1:rows, j in 1:cols
        u, v = vars[i], baseparams[j]
        if u == v
            A[i,j] = j == findfirst(x->x==u, baseparams) ? 1 : 0
        else
            A[i,j] = findfirst(x->x==u, baseparams) === nothing ? mkvar("a$i$j") : 0
        end
    end
    A
end

symroot(n::Int) = [mkvar("w$i") for i in 1:n]

# ------------------------------------------------------------------------------

"Generate constraints describing the relationship between entries of B and the closed forms."
function cstr_cforms(ctx::SynthContext)
    rows = size(ctx.body, 1)
    t = length(ctx.roots)
    B, rs, ms = ctx.body, ctx.roots, ctx.multi
    Ds = [sum(binomial(k-1, j-1) * coeffvec(i, k, rows, params=ctx.params) * rs[i] for k in j:ms[i]) - B * coeffvec(i, j, rows, params=ctx.params) for i in 1:t for j in 1:ms[i]]
    ps = destructpoly(collect(Iterators.flatten(Ds)), ctx.params)
    ClauseSet(map(Clause ∘ Constraint{EQ}, ps))
end

"Generate constraints defining the initial values."
function cstr_init(ctx::SynthContext)
    B, rs, ms = ctx.body, ctx.roots, ctx.multi
    s = size(B, 1)
    d = sum(ms)
    A = ctx.init*ctx.params
    cstr = Poly[]
    for i in 0:d-1
        M = cforms(s, rs, ms, lc=i, exp=i, params=ctx.params)
        X = iszero(i) ? A : B^i*A
        append!(cstr, X - M)
    end
    ps = destructpoly(cstr, ctx.params)
    ClauseSet(map(Clause ∘ Constraint{EQ}, ps))
end

# function LinearAlgebra.det(M::Matrix{<:Poly}) 
#     m = size(M, 1)
#     if m > 2
#         return sum((-1)^(i-1) * M[i,1] *  det(M[1:end .!= i, 2:end]) for i in 1:m)
#     else
#         return M[1,1] * M[2,2] - M[2,1] * M[1,2]
#     end
# end

"Generate constraints ensuring that the root symbols are roots of the characteristic polynomial of B."
function cstr_roots(ctx::SynthContext)
    B, rs, ms = ctx.body, ctx.roots, ctx.multi
    λ = mkvar(gensym_unhashed(:x))
    BB = copy(B)
    for i in diagind(B)
        BB[i] = λ - BB[i]
    end
    cpoly = det(BB)
    factors = prod((λ - r)^m for (r, m) in zip(rs,ms))
    ps = destructpoly(cpoly - factors, λ)
    ClauseSet(map(Clause ∘ Constraint{EQ}, ps))
end

"Generate constraints ensuring that the elements of rs are distinct."
function cstr_distinct(ctx::SynthContext)
    ps = [r1-r2 for (r1,r2) in combinations(ctx.roots, 2)]
    ClauseSet(map(Clause ∘ Constraint{NEQ}, ps))
end

# ------------------------------------------------------------------------------

"Generate constraints ensuring that sequence is not constant, i.e. B*B*x0 != B*x0."
function cstr_nonconstant(ctx::SynthContext)
    A, B = ctx.init*ctx.params, ctx.body
    cs = B * B * A - B * A
    # do not consider variables which only occurr as initial variable in polys
    vars = program_variables(ctx.inv)
    filter!(!isinitvar, vars)
    nonloopvars = setdiff(ctx.vars, vars)
    inds = [i for (i, v) in enumerate(ctx.vars) if !(v in vars)]
    deleteat!(cs, inds)
    destructpoly(cs, ctx.params)
end

# ------------------------------------------------------------------------------

function coeffvec2(i::Int, j::Int, varidx::Int; params::Vector{<:Poly})
    nparams = length(params)

    # s = collect('c':'z')[i*j]
    # C = [Basic("$s$k$l") for k in 1:rows, l in 1:nparams]
    C = sum(mkvar("c$i$j$(varidx)$l") * p for (l,p) in enumerate(params))
    C
end

# function cforms(varcnt::Int, rs::Vector{<:Var}, ms::Vector{Int}; lc::Union{Int,Var}, exp::Int, params::Vector{<:Poly})
function closed_form(ctx::SynthContext, func, arg)
    rs, ms, lc = ctx.roots, ctx.multi, ctx.lc
    lcvar = Symbol(string(ctx.lc))
    var = mkvar(func)
    idx = findfirst(x->x==var, ctx.vars)
    nroots = length(rs)
    parg = mkpoly(arg)
    pairs = [replacement_pair(NExp{lcvar}(rs[i], parg)) for i in 1:nroots]
    poly = sum(coeffvec2(i, j, idx, params=ctx.params) * first(pairs[i]) * parg^(j-1) for i in 1:nroots for j in 1:ms[i])
    CFiniteExpr{lcvar}(poly, Dict(pairs))
end

"Generate constraints ensuring that p is an algebraic relation."
function cstr_algrel(ctx::SynthContext)
    res = constraint_walk(ctx.inv) do poly
        expr = function_walk(poly) do func, args
            @assert length(args) == 1 "Invariant not properly preprocessed"
            :($(closed_form(ctx, func, args[1])))
        end
        cfin = eval(expr)
        cstr = constraints(cfin; split_vars=Any[ctx.params; ctx.lc])
        :($cstr)
    end
    eval(res)
end