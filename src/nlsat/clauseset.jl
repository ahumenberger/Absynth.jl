export Constraint, Clause, ClauseSet
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

struct Constraint{ConstraintRel}
    poly::Union{Expr,Symbol,Number}

    function Constraint{ConstraintRel}(x) where {ConstraintRel}
        (x isa Expr || x isa Symbol || x isa Number) && return new{ConstraintRel}(x)
        new{ConstraintRel}(Meta.parse(string(x)))
    end
end

const Clause = Set{Constraint}
const ClauseSet = Set{Clause}

Clause(c::Constraint) = Clause([c])
ClauseSet(c::Clause) = ClauseSet([c])

Base.:~(c::Constraint{EQ}) = Constraint{NEQ}(c.poly)
Base.:~(c::Constraint{NEQ}) = Constraint{EQ}(c.poly)
Base.:~(c::Constraint{LT}) = Constraint{GEQ}(c.poly)
Base.:~(c::Constraint{LEQ}) = Constraint{GT}(c.poly)
Base.:~(c::Constraint{GT}) = Constraint{LEQ}(c.poly)
Base.:~(c::Constraint{GEQ}) = Constraint{LT}(c.poly)
Base.:|(x::Constraint, y::Constraint) = Clause([x, y])
Base.:&(x::Constraint, y::Constraint) = ClauseSet([Clause([x]), Clause([y])])

Base.:~(c::Clause) = ClauseSet([Clause([~x]) for x in c])
Base.:|(x::Clause, y::Clause) = Clause(union(x, y))
Base.:&(x::Clause, y::Clause) = ClauseSet([x, y])

Base.:~(cs::ClauseSet) = reduce(Base.:|, [~c for c in cs])
Base.:|(x::ClauseSet, y::ClauseSet) = ClauseSet(map(z->(z[1] | z[2]), Iterators.product(x, y)))
Base.:&(x::ClauseSet, y::ClauseSet) = union(x, y)

Base.:|(x, y) = Base.:|(promote(x, y)...)
Base.:&(x, y) = Base.:&(promote(x, y)...)

Base.convert(::Type{Clause}, c::Constraint) = Clause([c])
Base.convert(::Type{ClauseSet}, c::Constraint) = ClauseSet([Clause([c])])
Base.convert(::Type{ClauseSet}, c::Clause) = ClauseSet([c])

Base.convert(::Type{Expr}, c::Constraint{EQ}) = :($(c.poly) == 0)
Base.convert(::Type{Expr}, c::Constraint{NEQ}) = :($(c.poly) != 0)
Base.convert(::Type{Expr}, c::Constraint{LT}) = :($(c.poly) < 0)
Base.convert(::Type{Expr}, c::Constraint{LEQ}) = :($(c.poly) <= 0)
Base.convert(::Type{Expr}, c::Constraint{GT}) = :($(c.poly) > 0)
Base.convert(::Type{Expr}, c::Constraint{GEQ}) = :($(c.poly) >= 0)
Base.convert(::Type{Expr}, c::Clause) = length(c) == 1 ? convert(Expr, first(c)) : Expr(:call, :|, [convert(Expr, x) for x in c]...)
Base.convert(::Type{Expr}, c::ClauseSet) = Expr(:call, :&, [convert(Expr, x) for x in c]...)

Base.promote_rule(::Type{Clause}, ::Type{Constraint{R}}) where {R} = Clause
Base.promote_rule(::Type{Constraint{R}}, ::Type{Clause}) where {R} = Clause
Base.promote_rule(::Type{ClauseSet}, ::Type{Constraint{R}}) where {R} = ClauseSet
Base.promote_rule(::Type{Constraint{R}}, ::Type{ClauseSet}) where {R} = ClauseSet
Base.promote_rule(::Type{ClauseSet}, ::Type{Clause}) = ClauseSet
Base.promote_rule(::Type{Clause}, ::Type{ClauseSet}) = ClauseSet

variables(c::Constraint) = symbols(c.poly)
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
    compact = get(io, :compact, true)
    if compact
        print(io, "ClauseSet($(length(cs)) constraints)")
    else
        print(io, "$(length(cs))-element ClauseSet:")
        for c in cs
            print(io, "\n ")
            print(IOContext(io, :compact => true), c)
        end
    end
end