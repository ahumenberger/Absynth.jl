using Singular
using SymEngine

export Variety

struct Variety
    I::sideal

    function Variety(ps::Vector{Expr})
        fs = union((free_symbols.(ps))...)
        R, _ = PolynomialRing(QQ, string.(fs))
        gens = R.(ps)
        I = Ideal(R, gens)
        new(I)
    end
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
    intersection(I, J)
end

function Base.intersect(v::Variety, w::Variety)
    I, J = v.I, w.I
    if base_ring(I) != base_ring(J)
        I, J = common_base_ring(I, J)
    end
    I + J
end

function Base.:(-)(v::Variety, w::Variety)
    I, J = v.I, w.I
    if base_ring(I) != base_ring(J)
        I, J = common_base_ring(I, J)
    end
    quotient(I, J)
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
