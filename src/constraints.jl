
import SymEngine.Basic
import SymPy.Sym

SymPy.Sym(x::Basic) = sympify(string(x))
SymEngine.Basic(x::SymPy.Sym) = Basic(string(x))

# if SymEngine.libversion < VersionNumber(0,4)
    function coeffs(ex::Basic, x::Basic)
        Basic.(sympy.Poly(Sym(ex), Sym(x)).coeffs())
    end
# else
#     function coeffs(ex::Basic, x::Basic)
#         d = degree(ex, x)
#         [coeff(ex, x, i) for i in d:-1:0]
#     end
# end

function degree(ex::Basic, x::Basic)
    convert(Int, SymPy.degree(Sym(ex), gen=Sym(x)))
end

function simplify(x::Basic)
    Basic(SymPy.simplify(Sym(x)))
end

isconstant(x::Basic) = isempty(SymEngine.free_symbols(x))

# ------------------------------------------------------------------------------

@enum MatrixShape full upper uni

function dynamicsmatrix(size::Int, shape::MatrixShape)
    T = Basic
    if shape == full
        # full
        B = [T("b$i$j") for i in 1:size, j in 1:size]
    elseif shape == upper
        # upper triangular
        B = [j>=i ? T("b$i$j") : zero(T) for i in 1:size, j in 1:size]
    elseif shape == uni
        # unitriangular
        B = [j>i ? T("b$i$j") : i==j ? one(T) : zero(T) for i in 1:size, j in 1:size]
    end
    B
end

initvar(s::T) where {T<:Union{Symbol,Basic}} = T("$(string(s))00")
isinitvar(s::Union{Symbol,Basic}) = endswith(string(s), "00")
basevar(s::Union{Symbol,Basic}) = isinitvar(s) ? Basic(string(s)[1:end-2]) : s

function filtervars(fs::Vector{Basic})
    init = filter(isinitvar, fs)
    init, unique(map(basevar, fs))
end

# ------------------------------------------------------------------------------

to_expr(xs::Vector{Basic}) = map(x->convert(Expr, x), xs)

eq(x::Basic, y::Basic=zero(Basic)) = Expr(:call, :(==), convert(Expr, x), convert(Expr, y))
ineq(x::Basic, y::Basic=zero(Basic)) = Expr(:call, :(!=), convert(Expr, x), convert(Expr, y))
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
    polys::Vector{Basic}
    vars::Vector{Basic}
    params::Vector{Basic}
    roots::Vector{Basic}
    multi::Vector{Int}
    body::Matrix{Basic}
    init::Vector{Basic}
    lc::Basic
end

function mkcontext(body::Matrix{Basic}, polys::Vector{Basic}, vars::Vector{Basic}, params::Vector{Basic}, ms::Vector{Int})
    rs, lc = symroot(length(ms)), Basic(gensym_unhashed(:n))
    SynthContext(polys, vars, params, rs, ms, body, map(initvar, vars), lc)
end

# ------------------------------------------------------------------------------

function raw_constraints(ctx::SynthContext)
    # Equality constraints
    cscforms = cstr_cforms(ctx)
    csinit   = cstr_init(ctx)
    csroots  = cstr_roots(ctx)
    csrel    = cstr_algrel(ctx)
    equalities = [collect(Iterators.flatten(cscforms)); csinit; csroots; csrel]
    @debug "Equality constraints" cscforms csinit csroots csrel

    # Inequality constraints
    csdistinct = cstr_distinct(ctx)
    inequalities = csdistinct
    @debug "Inequality constraints" csdistinct

    rs, ms = ctx.roots, ctx.multi
    t = length(ms)
    cs = Iterators.flatten(symconst(i, j, size(ctx.body, 1), params=ctx.params) for i in 1:t for j in 1:ms[i]) |> collect
    cs = SymEngine.free_symbols(cs)
    cs = setdiff(cs, ctx.params)
    bs = Iterators.flatten(ctx.body) |> collect
    vars = [cs; rs]
    varmap = convert(Dict{Symbol,Type}, Dict(Symbol(string(v))=>AlgebraicNumber for v in vars))
    for b in bs
        if !isconstant(b)
            push!(varmap, Symbol(string(b))=>AlgebraicNumber)
        end
    end
    for v in ctx.init
        if !isconstant(v) && !(v in ctx.params)
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

function cforms(varcnt::Int, rs::Vector{Basic}, ms::Vector{Int}; lc::Basic, exp::Basic, params::Vector{Basic})
    t = length(rs)
    sum(symconst(i, j, varcnt, params=params) * rs[i]^exp * lc^(j-1) for i in 1:t for j in 1:ms[i])
end

function symconst(i::Int, j::Int, rows::Int; params::Vector{Basic})
    nparams = length(params) + 1
    params = [params; one(Basic)]

    # s = collect('c':'z')[i*j]
    # C = [Basic("$s$k$l") for k in 1:rows, l in 1:nparams]
    C = [Basic("c$i$j$k$l") for k in 1:rows, l in 1:nparams]
    C * params
end

symroot(n::Int) = [Basic("w$i") for i in 1:n]

# ------------------------------------------------------------------------------

"Generate constraints describing the relationship between entries of B and the closed forms."
function cstr_cforms(ctx::SynthContext)
    rows = size(ctx.body, 1)
    t = length(ctx.roots)
    B, rs, ms = ctx.body, ctx.roots, ctx.multi
    Ds = [sum(binomial(k-1, j-1) * symconst(i, k, rows, params=ctx.params) * rs[i] for k in j:ms[i]) - B * symconst(i, j, rows, params=ctx.params) for i in 1:t for j in 1:ms[i]]
    destructpoly(Iterators.flatten(Ds), ctx.params)
end

"Generate constraints defining the initial values."
function cstr_init(ctx::SynthContext)
    B, rs, ms = ctx.body, ctx.roots, ctx.multi
    s = size(B, 1)
    d = sum(ms)
    A = ctx.init
    cstr = Basic[]
    for i in 0:d-1
        M = cforms(s, rs, ms, lc=Basic(i), exp=Basic(i), params=ctx.params)
        X = B^i*A
        append!(cstr, X - M)
    end
    destructpoly(cstr, ctx.params)
end

# LinearAlgebra.det(m::Matrix{Basic}) = det(convert(SymEngine.CDenseMatrix, m))

function LinearAlgebra.det(M::Matrix{Basic}) 
    m = size(M, 1)
    if m > 2
        return sum((-1)^(i-1) * M[i,1] *  det(M[1:end .!= i, 2:end]) for i in 1:m)
    else
        return M[1,1] * M[2,2] - M[2,1] * M[1,2]
    end
end

"Generate constraints ensuring that the root symbols are roots of the characteristic polynomial of B."
function cstr_roots(ctx::SynthContext)
    B, rs = ctx.body, ctx.roots
    λ = Basic("lbd")
    cpoly = det(B-UniformScaling(λ)) |> simplify
    cstr = [SymEngine.subs(cpoly, λ=>r) for r in rs]
    cstr
end

"Generate constraints ensuring that the elements of rs are distinct."
cstr_distinct(ctx::SynthContext) = [r1-r2 for (r1,r2) in combinations(ctx.roots, 2)]

# ------------------------------------------------------------------------------

"Generate constraints ensuring that sequence is not constant, i.e. B*B*x0 != B*x0."
function cstr_nonconstant(ctx::SynthContext)
    A, B = ctx.init, ctx.body
    cs = B * B * A - B * A
    destructpoly(cs, ctx.params)
end

# ------------------------------------------------------------------------------

"Generate constraints ensuring that p is an algebraic relation."
function cstr_algrel(ctx::SynthContext)
    B, rs, ms = ctx.body, ctx.roots, ctx.multi

    cfs = cforms(size(B, 1), rs, ms, lc=ctx.lc, exp=one(Basic), params=ctx.params)
    d = Dict(zip(ctx.vars, cfs))

    cs = Basic[]
    for p in ctx.polys
        p = SymEngine.subs(p, d...)
        qs = destructpoly(p, ctx.lc)
        for (i, q) in enumerate(qs)
            ms, us = destructterm(q, rs)
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

destructpoly(p::Basic, var::Basic) = coeffs(p, var)
destructpoly(p::Basic, var::Basic, left::Basic...) = 
    reduce(union, map(x->destructpoly(x, left...), coeffs(p, var)))

destructpoly(ps, vars::Vector{Basic}) =
    isempty(vars) ? ps : reduce(union, map(x->destructpoly(x, vars...), ps))

function destructterm(p::Basic, rs::Vector{Basic})
    ms = Basic[]
    cs = Basic[]
    for term in get_args(SymEngine.expand(p))
        ds = [degree(term, r) for r in rs]
        m = prod(r^d for (r,d) in zip(rs,ds))
        c = term / m
        push!(ms, m)
        push!(cs, c)
    end
    factor(ms, cs)
end

function factor(ms::Vector{Basic}, us::Vector{Basic})
    map = Dict{Basic,Basic}()
    for (m,u) in zip(ms,us)
        if haskey(map, m)
            map[m] += u
        else
            map[m] = u
        end
    end
    keys(map), Base.values(map)
end


