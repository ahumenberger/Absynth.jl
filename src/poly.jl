export mkvar, mkpoly

const PolyT = Polynomial{true,Float64}

mkpoly(x::Expr) = eval(symbol_walk(y->mkvar(y), x)) * one(PolyT)
mkpoly(x::Symbol) = mkvar(x) * one(PolyT)
mkpoly(x::Number) = iszero(x) ? zero(PolyT) : one(PolyT) * x
mkpoly(x::T) where {T<:AbstractVariable} = x * one(PolyT)

_varmap = Dict{Symbol, AbstractVariable}()

mkvar(x::String) = mkvar(Symbol(x))
mkvar(x::T) where {T <: AbstractVariable} = x
function mkvar(x::Symbol)
    if haskey(_varmap, x)
        return _varmap[x]
    end
    v = PolyVar{true}(string(x))
    push!(_varmap, x=>v)
    v
end

MultivariatePolynomials.isconstant(p::AbstractPolynomialLike) = all(isconstant, terms(p))