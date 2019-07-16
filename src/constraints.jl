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

function filtervars(fs::Vector{<:Var})
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

gensym_unhashed(s::Symbol) = Symbol(replace(string(gensym(s)), "#"=>""))

# ------------------------------------------------------------------------------

struct SynthContext
    polys::Vector{<:Poly}
    vars::Vector{<:Var}
    params::Vector{<:Poly}
    roots::Vector{<:Var}
    multi::Vector{Int}
    body::Matrix{<:Poly}
    init::Matrix{<:Poly}
    lc::Var
end

function mkcontext(body::Matrix{<:Poly}, init::Matrix{<:Poly}, polys::Vector{<:Poly}, vars::Vector{<:Var}, params::Vector{<:Var}, ms::Vector{Int})
    rs, lc = symroot(length(ms)), mkvar(gensym_unhashed(:n))
    SynthContext(polys, vars, [params; mkpoly(1)], rs, ms, body, init, lc)
end

# ------------------------------------------------------------------------------

function raw_constraints(ctx::SynthContext)
    # Equality constraints
    cscforms = cstr_cforms(ctx)
    csinit   = cstr_init(ctx)
    csroots  = cstr_roots(ctx)
    csrel    = cstr_algrel(ctx)
    @info "Equality constraints" cscforms csinit csroots csrel
    equalities = Poly[cscforms; csinit; csroots; csrel]

    # Inequality constraints
    csdistinct = cstr_distinct(ctx)
    inequalities = csdistinct
    @debug "Inequality constraints" csdistinct

    rs, ms = ctx.roots, ctx.multi
    t = length(ms)
    cs = Iterators.flatten(coeffvec(i, j, size(ctx.body, 1), params=ctx.params) for i in 1:t for j in 1:ms[i]) |> collect
    # cs = union(variables.(cs))
    cs = reduce(union, map(variables, cs))
    cs = setdiff(cs, ctx.params)
    bs = reduce(union, map(variables, ctx.body))
    @info "" rs cs bs
    vars = [cs; rs]
    varmap = convert(Dict{Symbol,Type}, Dict(Symbol(string(v))=>AlgebraicNumber for v in vars))
    for b in bs
        # if !isconstant(b)
            push!(varmap, Symbol(string(b))=>AlgebraicNumber)
        # end
    end
    for v in ctx.init
        # if !isconstant(v) && !(v in ctx.params)
        if !(v in ctx.params)
            push!(varmap, Symbol(string(v))=>AlgebraicNumber)
        end
    end
    @debug "Variables" varmap

    if !(latex_logger() isa NullLogger)
        with_logger(latex_logger()) do

            function subscript(s)
                str = string(s)
                if !occursin("_", str)
                    i = findfirst(x->x in '0':'9', str)
                    return Basic(join([str[1:i-1], "_", str[i:end]]))
                end
                Basic(str)
            end

            sdict = Dict(Basic(v)=>subscript(v) for v in keys(varmap))

            function beautify(x)
                # x = SymEngine.subs(x, Basic("t00")=>1, Basic("w1")=>1, Basic("q00")=>Basic("q_0"))
                x = SymEngine.subs(x, sdict...)
                x = simplify(x)
                startswith(string(x), "-") ? simplify(-x) : x
            end

            lalign(vec) = latexalign(vec, zeros(Basic, length(vec)), cdot=false)
            lcforms = lalign(map(beautify, cscforms))
            linit   = lalign(map(beautify, csinit))
            lroots  = lalign(map(beautify, csroots))
            lrel    = lalign(map(beautify, csrel))
            @info "Equality constraints" lcforms linit lroots lrel
        end
    end

    varmap, equalities, inequalities
end

function constraints(ctx::SynthContext)
    varmap, equalities, inequalities = raw_constraints(ctx)
    varmap, [map(eq, equalities); map(ineq, inequalities)]
end

function constraints_opt(ctx::SynthContext)
    cstr = map(ineq, cstr_nonconstant(ctx))
    [or(cstr...)]
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
    # @info "" Ds Iterators.flatten(Ds) |> collect
    destructpoly(collect(Iterators.flatten(Ds)), ctx.params)
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
    destructpoly(cstr, ctx.params)
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
    @info "" BB
    cpoly = det(BB)
    factors = prod((λ - r)^m for (r, m) in zip(rs,ms))
    destructpoly(cpoly - factors, λ)
end

"Generate constraints ensuring that the elements of rs are distinct."
cstr_distinct(ctx::SynthContext) = [r1-r2 for (r1,r2) in combinations(ctx.roots, 2)]

# ------------------------------------------------------------------------------

"Generate constraints ensuring that sequence is not constant, i.e. B*B*x0 != B*x0."
function cstr_nonconstant(ctx::SynthContext)
    A, B = ctx.init*ctx.params, ctx.body
    cs = B * B * A - B * A
    # do not consider variables which only occurr as initial variable in polys
    vars = reduce(union, map(variables, ctx.polys))
    filter!(!isinitvar, vars)
    nonloopvars = setdiff(ctx.vars, vars)
    inds = [i for (i, v) in enumerate(ctx.vars) if !(v in vars)]
    deleteat!(cs, inds)
    destructpoly(cs, ctx.params)
end

# ------------------------------------------------------------------------------

"Generate constraints ensuring that p is an algebraic relation."
function cstr_algrel(ctx::SynthContext)
    B, rs, ms = ctx.body, ctx.roots, ctx.multi

    cfs = cforms(size(B, 1), rs, ms, lc=ctx.lc, exp=1, params=ctx.params)
    dcfs = Dict(zip(ctx.vars, cfs))

    dinit = Dict(zip(map(initvar, ctx.vars), ctx.init*ctx.params))

    cs = Poly[]
    for p in ctx.polys
        p = MultivariatePolynomials.subs(p, dcfs..., dinit...)
        @info "" p
        qs = destructpoly(p, ctx.lc)
        for (i, q) in enumerate(qs)
            ms, us = destructterm(q, rs)
            @assert sum(m*u for (m,u) in zip(ms,us)) == q "Factorization bug"
            l = length(ms)
            if all(isone, ms)
                l = 1
            end
            c = [sum(m^j*u for (m,u) in zip(ms,us)) for j in 0:l-1]
            append!(cs, c)
        end
    end
    destructpoly(cs, ctx.params)
end

# ------------------------------------------------------------------------------

coeffs(p::Poly, v::Var) = [coefficient(p, v^i, [v]) for i in 0:maxdegree(p, v)]

destructpoly(p::Poly, var::Var) = coeffs(p, var)
destructpoly(p::Poly, var::Var, left::Var...) = 
    reduce(union, map(x->destructpoly(x, left...), coeffs(p, var)))

function destructpoly(ps, vars)
    xvars = filter(x->isa(x, Var), vars)
    isempty(xvars) ? ps : reduce(union, map(x->destructpoly(x, xvars...), ps))
end

function destructterm(p::Poly, rs::Vector{<:Var})
    ms = Poly[]
    cs = Poly[]
    for term in terms(p)
        ds = [maxdegree(term, r) for r in rs]
        m = prod(r^d for (r,d) in zip(rs,ds))
        c = div(term, m)
        @info "" m c
        push!(ms, m)
        push!(cs, c)
    end
    factor(ms, cs)
end

function factor(ms::Vector{<:Poly}, us::Vector{<:Poly})
    map = Dict{Poly,Poly}()
    for (m,u) in zip(ms,us)
        if haskey(map, m)
            map[m] += u
        else
            map[m] = u
        end
    end
    keys(map), Base.values(map)
end

# function summands(x::Basic)
#     args = get_args(SymEngine.expand(x))
#     sum(args) == x ? args : x
# end