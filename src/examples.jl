export examples, example

macro example(name, inv)
    push!(_examples, name=>parseformula(inv))
end

_examples = Dict{Symbol,Vector{Expr}}()

examples() = _examples
example(s) = _examples[s]

@example intcubicroot (1/4 + 3*r^2 == s && 1 + 4*x00+6*r^2 == 3*r+4*r^3+4*x)
@example cubes        (n^3 == x && 1 + 3*n + 3*n^2 == y && 6 + 6*n == z)
@example intsqrt1     (j == 2*k+1 && (1+j)^2 == 4*m)
@example intsqrt2     (y00*2 + r == r^2 + 2*y)
@example dijkstra     (r + q*y00 == r00)
@example ex1          (a == b^2)
@example ex2          (1 + 2*a == c && 4*b == (c-1)^2)
@example ex3          (1 + 2*a == c && b + c == 1 + s && c*(c+2) == 3 + 4*s)