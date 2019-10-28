using ParserCombinator

struct SExpr
    vec
end

expr         = Delayed()
floaty       = p"[-+]?[0-9]*\.[0-9]+([eE][-+]?[0-9]+)?" > (x -> parse(Float32, x[1:end]))
opt_ws       = p"\s" | e""
inty         = p"[-+]?\d+" > (x -> parse(Int, x))
raty         = inty + E"/" + inty > Rational{Int}
booly        = p"(true|false)" > (x -> x == "true" ? true : false)
symboly      = p"[^\d(){}#'`,@~;~\[\]\s][^\s()#'`,@~;{}~\[\]]*" > Symbol
sexpr        = E"(" + ~opt_ws + Repeat(expr + ~opt_ws) + E")" |> (x -> SExpr(x))

expr.matcher =  floaty | raty | inty | booly | symboly | sexpr

top_level    = Repeat(~opt_ws + expr) + ~opt_ws + Eos()

function parse_sexpr(s::String)
  x = parse_one(s, expr)
  x[1]
end


