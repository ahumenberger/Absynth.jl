export AbstractConstraint, CFiniteConstraint, Constraint, Clause, ClauseSet
export EQ, NEQ, LT, LEQ, GT, GEQ
export variables

@enum ConstraintRel EQ NEQ LT LEQ GT GEQ

_constraintrel_map = Dict(
    EQ  => :(==),
    NEQ => :(!=),
    LT  => :(<),
    LEQ => :(<=),
    LT  => :(>),
    LEQ => :(>=)
)

const XExpr = Union{Expr,Symbol,Number}

abstract type AbstractConstraint end
const Clause = OrderedSet{AbstractConstraint}
const ClauseSet = OrderedSet{Clause}

struct CFiniteConstraint{R} <: AbstractConstraint
    us::Vector{XExpr}
    ms::Vector{XExpr}

    function CFiniteConstraint{R}(us, ms) where {R}
        @assert R == EQ || R == NEQ
        @assert length(us) == length(ms)
        _us = [Meta.parse(string(u)) for u in us]
        _ms = [Meta.parse(string(m)) for m in ms]
        new(_us, _ms)
    end
end

Base.:~(c::CFiniteConstraint{EQ}) = CFiniteConstraint{NEQ}(c.us, c.ms)
Base.:~(c::CFiniteConstraint{NEQ}) = CFiniteConstraint{EQ}(c.us, c.ms)

function expand(c::CFiniteConstraint{R}) where {R}
    cs = ClauseSet()
    for i in 1:length(c.us)
        ms = map(x->:($x^($i-1)), c.ms)
        terms = [:($u*$m) for (u,m) in zip(c.us,ms)]
        if length(terms) == 1
            cs &= Constraint{EQ}(terms[1])
        else
            cs &= Constraint{EQ}(Expr(:call, :+, terms...))
        end
    end
    R == NEQ ? ~cs : cs
end

expand(c::T) where {T<:AbstractConstraint} = ClauseSet(Clause(c))
expand(c::Clause) = foldl(|, (expand(x) for x in c))
expand(c::ClauseSet) = foldl(&, (expand(x) for x in c))

struct Constraint{ConstraintRel} <: AbstractConstraint
    poly::Union{Expr,Symbol,Number}

    function Constraint{ConstraintRel}(x) where {ConstraintRel}
        (x isa Expr || x isa Symbol || x isa Number) && return new{ConstraintRel}(x)
        new{ConstraintRel}(Meta.parse(string(x)))
    end
end

Clause(c::AbstractConstraint) = Clause([c])
ClauseSet(c::Clause) = ClauseSet([c])

Base.:~(c::Constraint{EQ}) = Constraint{NEQ}(c.poly)
Base.:~(c::Constraint{NEQ}) = Constraint{EQ}(c.poly)
Base.:~(c::Constraint{LT}) = Constraint{GEQ}(c.poly)
Base.:~(c::Constraint{LEQ}) = Constraint{GT}(c.poly)
Base.:~(c::Constraint{GT}) = Constraint{LEQ}(c.poly)
Base.:~(c::Constraint{GEQ}) = Constraint{LT}(c.poly)

Base.:|(x::AbstractConstraint, y::AbstractConstraint) = Clause([x, y])
Base.:&(x::AbstractConstraint, y::AbstractConstraint) = ClauseSet([Clause([x]), Clause([y])])

Base.:~(c::Clause) = ClauseSet([Clause([~x]) for x in c])
Base.:|(x::Clause, y::Clause) = Clause(union(x, y))
Base.:&(x::Clause, y::Clause) = ClauseSet([x, y])

Base.:~(cs::ClauseSet) = reduce(Base.:|, [~c for c in cs])
Base.:|(x::ClauseSet, y::ClauseSet) = ClauseSet(map(z->(z[1] | z[2]), Iterators.product(x, y)))
Base.:&(x::ClauseSet, y::ClauseSet) = union(x, y)

Base.:|(x, y) = Base.:|(promote(x, y)...)
Base.:&(x, y) = Base.:&(promote(x, y)...)

Base.convert(::Type{Clause}, c::AbstractConstraint) = Clause([c])
Base.convert(::Type{ClauseSet}, c::AbstractConstraint) = ClauseSet([Clause([c])])
Base.convert(::Type{ClauseSet}, c::Clause) = ClauseSet([c])

Base.convert(::Type{Expr}, c::Constraint{EQ}) = :($(c.poly) == 0)
Base.convert(::Type{Expr}, c::Constraint{NEQ}) = :($(c.poly) != 0)
Base.convert(::Type{Expr}, c::Constraint{LT}) = :($(c.poly) < 0)
Base.convert(::Type{Expr}, c::Constraint{LEQ}) = :($(c.poly) <= 0)
Base.convert(::Type{Expr}, c::Constraint{GT}) = :($(c.poly) > 0)
Base.convert(::Type{Expr}, c::Constraint{GEQ}) = :($(c.poly) >= 0)
Base.convert(::Type{Expr}, c::Clause) = length(c) == 1 ? convert(Expr, first(c)) : Expr(:call, :|, [convert(Expr, x) for x in c]...)
Base.convert(::Type{Expr}, c::ClauseSet) = Expr(:call, :&, [convert(Expr, x) for x in c]...)

Base.promote_rule(::Type{Clause}, ::Type{<:AbstractConstraint}) = Clause
Base.promote_rule(::Type{<:AbstractConstraint}, ::Type{Clause}) = Clause
Base.promote_rule(::Type{ClauseSet}, ::Type{<:AbstractConstraint}) = ClauseSet
Base.promote_rule(::Type{<:AbstractConstraint}, ::Type{ClauseSet}) = ClauseSet
Base.promote_rule(::Type{ClauseSet}, ::Type{Clause}) = ClauseSet
Base.promote_rule(::Type{Clause}, ::Type{ClauseSet}) = ClauseSet

variables(c::Constraint) = symbols(c.poly)
variables(c::CFiniteConstraint) = union((symbols(x) for x in c.us)..., (symbols(x) for x in c.ms)...) 
variables(c::Clause) = union((variables(x) for x in c)...)
variables(c::ClauseSet) = union((variables(x) for x in c)...)

function Base.show(io::IO, c::Constraint{R}) where {R}
    print(io, c.poly)
    print(io, " ")
    print(io, string(_constraintrel_map[R]))
    print(io, " 0")
end

function Base.show(io::IO, c::Clause)
    compact = get(io, :compact, false)
    if compact
        print(io, string("[", join(c, ", "), "]"))
    else
        print(io, "$(length(c))-element Clause:")
        for x in c
            print(io, "\n ")
            print(io, x)
        end
    end
end

function Base.show(io::IO, cs::ClauseSet)
    print(io, "$(length(cs))-element ClauseSet:")
    for c in cs
        print(io, "\n ")
        print(IOContext(io, :compact => true), c)
    end
end