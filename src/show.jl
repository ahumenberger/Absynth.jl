
to_assignments(xs::Vector, ys::Vector) = ["$x = $y" for (x, y) in zip(xs, ys)]
to_lines(xs::Vector{String}, indent::Int) = join(xs, "\n$(repeat("    ", indent))")
to_list(xs) = join(xs, ", ")

prettify_number(x::Rational) = iszero(numerator(x)) || isone(denominator(x)) ? numerator(x) : x
prettify_number(x::Poly) = iszero(x) ? 0 : isconstant(x) ? prettify_number(coefficient(x[1])) : x
prettify_number(x) = x

Base.alignment(io::IO, x::Symbol) = (length(sprint(show, x, context=io, sizehint=0)), 0)
Base.alignment(io::IO, x::Poly) = (length(sprint(show, x, context=io, sizehint=0)), 0)

# ------------------------------------------------------------------------------

lpar(h::Int, d = "") = h == 1 ? "($(d)" : join(["⎛$(d)"; fill("⎜$(d)", h - 2); "⎝$(d)"], "\n")
rpar(h::Int, d = "") = h == 1 ? "$(d))" : join(["$(d)⎞"; fill("$(d)⎟", h - 2); "$(d)⎠"], "\n")

space(h::Int, sp = " ") = join(fill(sp, h), "\n")

function symstr(h::Int, symbol::String)
    a = fill("   ", h)
    a[Int(ceil(h/2))] = " $(symbol) "
    return join(a, "\n")
end

function mergestr(strings::String...)
    splits = split.(strings, "\n")
    rows = length(splits[1])
    cols = length(splits)
    matr = reshape(collect(Iterators.flatten(splits)), rows, cols)
    join([join(matr[i,:]) for i in 1:size(matr, 1)], "\n")
end

# ------------------------------------------------------------------------------

function _print_recsystem(io::IO, vars, body, init)
    h = size(body, 1)
    lstr, rstr = lpar(h), rpar(h, " ")
    eq = symstr(h, "=")

    # lc = "\u2099"
    # lp, rp, plus = "", "", "\u208A" 
    # zero, one = "\u2080", "\u2081"

    lc = "n"
    lp, rp, plus = "(", ")", "+" 
    zero, one = "0", "1"

    _vars = sprint(Base.print_matrix, vars)
    # vars0 = Base.replace(sprint(Base.print_matrix, map(x->string(x)*"$lp$zero$rp", vars)), "\""=>"")
    # vars1 = Base.replace(sprint(Base.print_matrix, map(x->string(x)*"$lp$lc$rp", vars)), "\""=>"")
    # vars2 = Base.replace(sprint(Base.print_matrix, map(x->string(x)*"$lp$lc$plus$one$rp", vars)), "\""=>"")
    vars0 = Base.replace(_vars, "\n"=>"$lp$zero$rp\n") * "$lp$zero$rp"
    vars1 = Base.replace(_vars, "\n"=>"$lp$lc$rp\n") * "$lp$lc$rp"
    vars2 = Base.replace(_vars, "\n"=>"$lp$lc$plus$one$rp\n") * "$lp$lc$plus$one$rp"
    vars0 = Base.replace(vars0, ":"=>"")
    vars1 = Base.replace(vars1, ":"=>"")
    vars2 = Base.replace(vars2, ":"=>"")
    body = map(prettify_number, body)
    init = map(prettify_number, init)
    body = sprint(Base.print_matrix, body)
    init = sprint(Base.print_matrix, init)

    lhs1 = (lstr, vars2, rstr)
    rhs1 = (lstr, body, rstr, lstr, vars1, rstr)

    lhs2 = (lstr, vars0, rstr)
    rhs2 = (lstr, init, rstr)
    str = mergestr(space(h, "\t"), lhs1..., eq, rhs1..., space(h, "\t"), lhs2..., eq, rhs2...)
    print(io, str)
end