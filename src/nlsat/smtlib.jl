using MacroTools, DataStructures

op_map = Dict(
    :+    => :smt_plus,
    :-    => :smt_minus,
    :*    => :smt_mult,
    :^    => :smt_pow,
    :(==) => :smt_eq,
    :(!=) => :smt_neq,
    :(&)  => :smt_and,
    :(|)  => :smt_or
)

lookup!(d, x::Number) = x < 0 ? "(- $((abs(x))))" : string((x))
lookup!(d, x::Symbol) = get(op_map, x, string(x))

function lookup!(d, x::Expr)
    x.head != :call && return x
    haskey(d, x) && return string(d[x])
    s = gensym_unhashed(:t)
    push!(d, x=>s)
    string(s)
end

function cse(expr::Expr)
    d = OrderedDict()
    _expr = MacroTools.postwalk(expr) do x
        lookup!(d, x)
    end
    d, _expr
end

preprocess_smt(x) = postwalk(x) do y
    @match y begin
        b_^e_ => Expr(:call, :*, fill(b, e)...)
        _     => y
    end
end

function smt(cs::ClauseSet; expand_pow::Bool=false)
    expr = convert(Expr, cs)
    expr = expand_pow ? preprocess_smt(expr) : expr
    d, x = cse(expr)
    ls = [:(smt_assign($(string(v)), $k)) for (k,v) in d]
    push!(ls, :(string($x)))
    x = foldr((x,y)->:(smt_nest($x,$y)), ls)
    eval(:(smt_assert($x)))
end

smt_plus(x...)   = "(+ $(join(x, " ")))"
smt_mult(x...)   = "(* $(join(x, " ")))"
smt_and(x...)    = "(and $(join(x, " ")))"
smt_or(x...)     = "(or $(join(x, " ")))"
smt_eq(x, y)     = "(= $x $y)"
smt_neq(x, y)    = "(distinct $x $y)"
smt_pow(x, y)    = "(^ $x $y)"
smt_minus(x, y)  = "(- $x $y)"
smt_minus(x)     = "(- $x)"
smt_assign(x, y) = "(($x $y))"
smt_nest(x, y)   = "(let $x \n$y)"
smt_assert(x)    = "(assert \n$x)"