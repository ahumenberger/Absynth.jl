using ParserCombinator

struct SExpr
    vec
end

expry         = Delayed()
floaty       = p"[-+]?[0-9]*\.[0-9]+([eE][-+]?[0-9]+)?" > (x -> parse(Float32, x[1:end]))
opt_ws       = p"\s" | e""
inty         = p"[-+]?\d+" > (x -> parse(Int, x))
raty         = inty + E"/" + inty > Rational{Int}
rooty        = E"(root-obj" + ~opt_ws + expry + ~opt_ws + inty + E")" > ((x,y)->AlgebraicNumber(to_expr(x), y))
booly        = p"(true|false)" > (x -> x == "true" ? true : false)
symboly      = p"[^\d(){}#'`,@~;~\[\]\s][^\s()#'`,@~;{}~\[\]]*" > Symbol
sexpr        = E"(" + ~opt_ws + Repeat(expry + ~opt_ws) + E")" |> (x -> SExpr(x))

expry.matcher =  floaty | raty | inty | booly | rooty | symboly | sexpr

top_level    = Repeat(~opt_ws + expry) + ~opt_ws + Eos()

to_expr(x) = x isa SExpr ? Expr(:call, map(to_expr, x.vec)...) : x

function parse_sexpr(s::String)
  x = parse_one(s, expry)
  x[1]
end