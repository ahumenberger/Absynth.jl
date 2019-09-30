export mkvar, mkpoly

mkpoly(x::Expr) = eval(symbol_walk(y->mkvar(y), x))
mkpoly(x::Symbol) = mkvar(x)
mkpoly(x::Number) = iszero(x) ? zero(Polynomial{true,Int}) : one(Polynomial{true,Int}) * x

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