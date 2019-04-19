using Singular
using SymEngine

export Variety

struct Variety
    I::sideal

    Variety(I::sideal) = new(I)

    function Variety(ps::Vector{Expr})
        if isempty(ps)
            R, _ = PolynomialRing(QQ, ["n"])
            return new(Ideal(R, ))
        end
        @info ps
        fs = union((free_symbols.(ps))...)
        R, _ = PolynomialRing(QQ, string.(fs))
        gens = spoly{Singular.n_Q}[R(p) for p in ps]
        @info gens
        I = Ideal(R, gens)
        new(I)
    end
end

function Variety(ps::Vector{Basic})
    @info "Basic" ps
    Variety(Expr[convert(Expr, p) for p in ps])
end

function common_base_ring(is::sideal...)
    allsyms = union([Singular.symbols(base_ring(I)) for I in is]...)
    R, _ = PolynomialRing(QQ, string.(allsyms))
    js = sideal[]
    for I in is
        syms = Singular.symbols(base_ring(I))
        perm = [findfirst(x->x==s, allsyms) for s in syms]
        gens = [Singular.permute_variables(I[i], perm, R) for i in 1:ngens(I)]
        push!(js, Ideal(R, gens))
    end
    js
    # js...
end

function Base.union(v::Variety, w::Variety)
    I, J = v.I, w.I
    if base_ring(I) != base_ring(J)
        I, J = common_base_ring(I, J)
    end
    Variety(intersection(I, J))
end

function Base.intersect(v::Variety, w::Variety)
    I, J = v.I, w.I
    if base_ring(I) != base_ring(J)
        I, J = common_base_ring(I, J)
    end
    Variety(I + J)
end

function Base.:(-)(v::Variety, w::Variety)
    I, J = v.I, w.I
    if base_ring(I) != base_ring(J)
        I, J = common_base_ring(I, J)
    end
    Variety(quotient(I, J))
end

function (R::PolyRing)(p::Expr)
    vs = gens(R)
    vs = [:($(Symbol(string(v))) = $v) for v in vs]
    q = quote
        let $(vs...)
            $(p)
        end
    end
    eval(q)
end
