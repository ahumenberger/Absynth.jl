struct NExp{S}
    base::Var
    exp::Union{Poly,Var}
end

function (x::NExp{S})(n::Int) where {S}
    exp = MultivariatePolynomials.subs(x.exp, mkvar(S)=>n)
    @assert isconstant(exp)
    ex = convert(Number, exp)
    x.base^ex
end

_exp_map = Dict{NExp,Var}()

function replacement_pair(exp::NExp)
    var = get(_exp_map, exp, mkvar(gensym_unhashed(:r)))
    _exp_map[exp] = var
    var=>exp
end

struct CFiniteExpr{S}
    poly::Poly
    subs::Dict{Var, NExp{S}}
end

function _merge(x::Dict{Var, NExp{S}}, y::Dict{Var, NExp{S}}) where {S}
    @assert isempty(intersect(keys(x), keys(y)))
    merge(x, y)
end

Base.:+(x::CFiniteExpr{S}, y::CFiniteExpr{S}) where {S} = CFiniteExpr{S}(x.poly + y.poly, merge(x.subs, y.subs))
Base.:-(x::CFiniteExpr{S}, y::CFiniteExpr{S}) where {S} = CFiniteExpr{S}(x.poly - y.poly, merge(x.subs, y.subs))
Base.:*(x::CFiniteExpr{S}, y::CFiniteExpr{S}) where {S} = CFiniteExpr{S}(x.poly * y.poly, merge(x.subs, y.subs))
Base.:^(x::CFiniteExpr{S}, y::Int) where {S} = CFiniteExpr{S}(x.poly^y, x.subs)

Base.:+(x, y) = Base.:+(promote(x, y)...)
Base.:-(x, y) = Base.:-(promote(x, y)...)
Base.:*(x, y) = Base.:*(promote(x, y)...)

Base.convert(::Type{CFiniteExpr{S}}, x::Number) where {S} = CFiniteExpr{S}(mkpoly(x), Dict{Var, NExp{S}}())

Base.promote_rule(::Type{CFiniteExpr{S}}, ::Type{<:Number}) where {S} = CFiniteExpr{S}
Base.promote_rule(::Type{<:Number}, ::Type{CFiniteExpr{S}}) where {S} = CFiniteExpr{S}

function (expr::CFiniteExpr{S})(n::Int) where {S}
    s = mkvar(S)
    newsubs = Dict(k=>v(n) for (k,v) in expr.subs)
    MultivariatePolynomials.subs(expr.poly, newsubs...)
end

function order(expr::CFiniteExpr)
    ms, us = destructterm(expr.poly, collect(keys(expr.subs)))
    @assert sum(m*u for (m,u) in zip(ms,us)) == expr.poly "Factorization bug"
    all(isone, ms) ? 1 : length(ms)
end

function constraints(expr::CFiniteExpr{S}; split_vars::Vector{Symbol}=Symbol[]) where {S}
    cs = ClauseSet()
    # qs = map(x->CFiniteExpr{S}(x, expr.subs), destructpoly(expr.poly, split_vars))
    qs = destructpoly([expr.poly], split_vars)
    for (i, q) in enumerate(qs)
        cfin = CFiniteExpr{S}(q, expr.subs)
        l = order(cfin)
        for i in 0:l-1
            ex = Meta.parse(string(cfin(i)))
            cs &= Constraint{EQ}(ex)
        end
        # Clauses capturing Cramer's rule
        ms, us = destructterm(cfin.poly, collect(keys(cfin.subs)))
        mclause = if length(ms) == 1
            Clause([Constraint{EQ}(Meta.parse(string(ms[1])))])
        else
            Clause([Constraint{EQ}(Meta.parse(string(m1-m2))) for (m1,m2) in combinations(ms, 2)])
        end
        cramer = ClauseSet([mclause | Constraint{EQ}(Meta.parse(string(u))) for u in us])
        # cs &= cramer

        # @info "" ms us
        for as in Combinatorics.combinations(zip(ms,us)|>collect)
            length(as) < 2 && continue
            fs = map(first, as)
            css = all_equal(fs)
            for f in fs
                css &= Constraint{NEQ}(f)
            end
            # @info "" css
            cstr = Constraint{EQ}(Meta.parse(string(sum(map(last, as)))))
            # @info "" css cstr (~css | cstr)
            # cs &= (~css | cstr)
        end
    end
    cs
end

all_equal(xs) = ClauseSet([Clause([Constraint{EQ}(Meta.parse(string(x-y)))]) for (x,y) in combinations(xs, 2)])

# ------------------------------------------------------------------------------

coeffs(p::Poly, v::Var) = [coefficient(p, v^i, [v]) for i in 0:maxdegree(p, v)]

destructpoly(p::Poly, var::Var) = coeffs(p, var)
destructpoly(p::Poly, var::Var, left::Var...) = 
    reduce(union, map(x->destructpoly(x, left...), coeffs(p, var)))

function destructpoly(ps, vars)
    xvars = map(mkvar, vars)
    isempty(xvars) ? ps : reduce(union, map(x->destructpoly(x, xvars...), ps))
end

function destructterm(p::Poly, rs::Vector{<:Var})
    ms = Poly[]
    cs = Poly[]
    for term in terms(p)
        ds = [maxdegree(term, r) for r in rs]
        m = prod(r^d for (r,d) in zip(rs,ds))
        c = div(term, m)
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
    collect(keys(map)), collect(Base.values(map))
end
