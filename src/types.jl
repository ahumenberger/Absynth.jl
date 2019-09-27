
export Invariant
export preprocess_invariant

abstract type Func end

struct VarFunc <: Func
    f::Symbol
    var::Symbol
    shift::Int
end

struct IntFunc <: Func
    f::Symbol
    arg::Int
end

struct Invariant
    poly::Union{Symbol,Expr}
    vmap::Dict{Symbol,Func}

    function Invariant(ex::Expr)
        d = Dict{Symbol,Func}()
        res = MacroTools.postwalk(ex) do x
            if @capture(x, f_(args__)) && Base.isidentifier(f)
                @info "" x f args
                length(args) != 1 && error("Too many arguments in $x")
                var = gensym_unhashed(f)
                if args[1] isa Int
                    fn = IntFunc(f, args[1])
                else
                    poly = mkpoly(args[1])
                    vars = variables(poly)
                    length(vars) != 1 && error("Too many loop counters, got $vars")
                    shift = poly - vars[1]
                    fn = VarFunc(f, Symbol(string(vars[1])), shift)
                end
                push!(d, var=>fn)
                return var
            end
            x
        end
        new(res, d)
    end
end

issymbol(x) = x isa Symbol && Base.isidentifier(x)
symbols(f, ex) = MacroTools.postwalk(x -> issymbol(x) ? f(x) : x, ex)
isfunction(x) = @capture(x, s_(xs__)) && s isa Symbol && Base.isidentifier(s)
functions(f, ex) = MacroTools.postwalk(x -> isfunction(x) ? f(x) : x, ex)

function _checkfunc(x, xs)
    x in [:(<), :(<=), :(>), :(>=)] && error("Only Boolean combinations of equalities allowed, got $x")
    if issymbol(x)
        length(xs) != 1 && error("Number of args does not match 1")
        symbols(xs[1]) do s
            s != :n && error("Only loop counter 'n' allowed")
        end
    end
    :($x($(xs...)))
end

function _checksym(x)
    issymbol(x) && return :($x(n))
    x
end

atomwalk(f, x) = MacroTools.walk(x, x -> (@capture(x, y_(ys__)) && issymbol(y)) ? f(x) : atomwalk(f, x) , f)

function preprocess_invariant(expr)
    atomwalk(expr) do ex
        @match ex begin
            x_ && y_ => :($x & $y)
            x_ || y_ => :($x | $y)
            x_ != 0  => :(~($x == 0))
            0 != x_  => :(~($x == 0))
            x_ != y_ => :(~($x-$y == 0))
            x_ == 0  => :($x == 0)
            0 == x_  => :($x == 0)
            x_ == y_ => :($x-$y == 0)
            x_(xs__) => _checkfunc(x, xs)
            _        => _checksym(ex)
        end
    end
end

constraint_walk(f, expr) = postwalk(expr) do x
    @capture(x, p_ == 0) ? f(p) : x
end

function_walk(f, expr) = postwalk(expr) do x
    @capture(x, g_(a_)) ? f(g, a) : x
end

# ------------------------------------------------------------------------------

struct NExp
    base
    exp
end

struct CFiniteExpr
    poly::Poly
    subs::Dict{Var, NExp}
end

function _merge(x::Dict{Var, NExp}, y::Dict{Var, NExp})
    @assert intersection(keys(x), keys(y))
    merge(x, y)
end

Base.:+(x::CFiniteExpr, y::CFiniteExpr) = CFiniteExpr(x.poly + x.poly, _merge(x.subs, y.subs))
Base.:-(x::CFiniteExpr, y::CFiniteExpr) = CFiniteExpr(x.poly - x.poly, _merge(x.subs, y.subs))