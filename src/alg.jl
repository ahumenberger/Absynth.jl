
using SymPy
using Combinatorics
using LinearAlgebra

symconst(i::Int, n::Int) = reshape([Basic("c$i$j") for j in 1:n], n, 1)
symroot(n::Int) = [Basic("w$i") for i in 1:n]

# ------------------------------------------------------------------------------

import SymEngine.Basic
import SymPy.Sym

SymPy.Sym(x::Basic) = Sym(string(x))
SymEngine.Basic(x::SymPy.Sym) = Basic(string(x))

function coeffs(ex::Basic, x::Basic)
    Basic.(SymPy.coeffs(Sym(ex), Sym(x)))
end

function degree(ex::Basic, x::Basic)
    convert(Int, SymPy.degree(Sym(ex), gen=Sym(x)))
end

simplify(x::Basic) = Basic(SymPy.simplify(Sym(x)))

isconstant(x::Basic) = isempty(SymEngine.free_symbols(x))

# ------------------------------------------------------------------------------

function constraints(inv::Basic)
    d = 2
    B = [Basic("b$i$j") for i in 1:d, j in 1:d]
    constraints(B, inv)
end

function constraints(B::Matrix{Basic}, inv::Basic)
    ms = ones(Int, size(B, 1))
    constraints(B, inv, ms)
end

function constraints(B::Matrix{Basic}, inv::Basic, ms::Vector{Int})
    rs = symroot(length(ms))
    cfs, cs = cforms(size(B, 1), rs, ms)
    p = SymEngine.lambdify(inv)(cfs...)
    vcforms = variety_cforms(B, cs, rs, ms)
    valgrel = variety_algrel(p, rs)
    @info "" vcforms valgrel
end

function cforms(n::Int, rs::Vector{Basic}, ms::Vector{Int}, lc::Basic=Basic("n"))
    ls = [r*lc^i for (r,m) in zip(rs,ms) for i in 0:m-1]
    cs = [symconst(i, n) for i in 1:length(ls)]
    sum(l*c for (l, c) in zip(ls, cs)), cs
end

symconst(i::Int, j::Int, n::Int) = reshape([Basic("c$i$j$k") for k in 1:n], n, 1)

function cfconst(ms, n)
    [symconst(i, j, n) for j in 1:length(ms), m in ms for i in 1:m]
end

function variety_cforms(B, cs, rs, ms)
    cstrs = Basic[]
    i = 1
    for (r,m) in zip(rs, ms)
        for j in 1:m
            cstr = binomial(m, j) * cs[i]*r - B*cs[i]
            @info "constraint" cstr
            push!(cstrs, vec(cstr)...)
            i += 1
        end
    end
    λ = Basic("lbd")
    cpoly = det(B-UniformScaling(λ)) |> simplify
    cps = [SymEngine.subs(cpoly, λ=>r) for r in rs]
    distinct = [r1-r2 for (r1,r2) in combinations(rs, 2)]
    @info "" cps distinct
    vroots = Variety(cps) - Variety(distinct)
    vcstrs = Variety(cstrs)
    intersect(vcstrs, vroots)
end

# ------------------------------------------------------------------------------

export TermPartition

struct TermPartition{T<:AbstractVector}
    a1::T
    a2::T
end

function Base.iterate(t::TermPartition)
    iter = partitions(1:length(t.a1), 2)
    next = iterate(iter)
    iterate(t, (iter, next, false))
end

function Base.iterate(t::TermPartition, s)
    (piter, next, reverse) = s
    if next !== nothing
        (part, pstate) = next
        if reverse
            (i1, i2) = part
        else
            (i2, i1) = part
        end
        s1 = [t.a1[i] for i in i1]
        s2 = [t.a2[i]-t.a2[j] for (i,j) in combinations(i2, 2)]
        @info "" s1 s2 i1 i2
        nextstate = !reverse ? (piter, next, true) : (piter, iterate(piter, pstate), false)
        return [s1; s2], nextstate
    elseif reverse == false
        return t.a1, (piter, next, true)
    elseif reverse == true
        return [x-y for (x,y) in combinations(t.a2, 2)], (piter, next, nothing)
    end
    return nothing
end

Base.IteratorSize(::Type{TermPartition{T}}) where {T<:AbstractVector} = Base.SizeUnknown()

# ------------------------------------------------------------------------------

struct TermVarieties
    ms::Vector{Basic}
    cs::Vector{Basic}
end

function Base.iterate(t::TermVarieties)
    iter = TermPartition(t.cs, t.ms)
    next = iterate(iter)
    iterate(t, (iter, next))
end

function Base.iterate(t::TermVarieties, s)
    (iter, next) = s
    if next !== nothing
        (ls, state) = next
        filter!(!iszero, ls)
        if any(isconstant, ls)
            return iterate(t, (iter, iterate(iter, state)))
        end
        return Variety(ls), (iter, iterate(iter, state))
    end
    return nothing
end

Base.IteratorSize(::Type{TermVarieties}) = Base.SizeUnknown()

# ------------------------------------------------------------------------------

function cstr_algrel(p::Basic, rs::Vector{Basic}, lc::Basic=Basic("n"))
    qs = destructpoly(p, lc)
    cs = Basic[]
    for (i, q) in enumerate(qs)
        ms, us = destructterm(q, rs)
        l = length(ms)
        c = [sum(m^j*u for (m,u) in zip(ms,us)) for j in 0:l-1]
        append!(cs, c)
    end
    cs
end

# ------------------------------------------------------------------------------

function destructpoly(p::Basic, lc::Basic=Basic("n"))
    coeffs(p, lc)
end

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
    ms, cs
end


