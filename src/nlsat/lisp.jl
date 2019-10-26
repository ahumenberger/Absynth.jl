using MacroTools, DataStructures

# expr = :((a^2 * (b+c) * (b+c) - 1 == 0) & (x ==0) & (y==9))

op_map = Dict(
    :+ => :smt_plus,
    :- => :smt_minus,
    :* => :smt_mult,
    :^ => :smt_pow,
    :(==) => :smt_eq,
    :(!=) => :smt_neq,
    :(&) => :smt_and,
    :(|) => :smt_or
)

lookup!(d, x::Number) = x

function lookup!(d, x::Symbol)
    get(op_map, x, string(x))
end

function lookup!(dict, x::Expr)
    x.head != :call && return x
    haskey(dict, x) && return string(dict[x])
    s = gensym()
    push!(dict, x=>s)
    string(s)
end

function cse(expr::Expr)
    d = OrderedDict()
    _expr = MacroTools.postwalk(expr) do x
        lookup!(d, x)
    end
    d, _expr
end

function smt(expr::Expr)
    d, x = cse(expr)
    ls = [:(smt_assign($(string(v)), $k)) for (k,v) in d]
    push!(ls, :(string($x)))
    x = foldr((x,y)->:(smt_nest($x,$y)), ls)
    :(smt_assert($x))
end

smt_plus(x...) = "(+ $(join(x, " ")))"
smt_mult(x...) = "(* $(join(x, " ")))"
smt_and(x...) = "(and $(join(x, " ")))"
smt_or(x...) = "(or $(join(x, " ")))"
smt_eq(x, y) = "(= $x $y)"
smt_neq(x, y) = "(distinct $x $y)"
smt_pow(x, y) = "(pow $x $y)"
smt_minus(x, y) = "(minus $x $y)"
smt_assign(x, y) = "(($x $y))"
smt_nest(x, y) = "(let $x \n$y)"
smt_assert(x) = "(assert \n$x)"