# export examples, example, varorders, varorder

# macro example(name, inv)
#     push!(_examples, name=>inv)
# end
# macro varorder(name, vars...)
#     push!(_varorder, name=>collect(vars))
# end

const Example = NamedTuple{(:name, :inv, :vars, :kwargs),Tuple{Symbol, Invariant, Vector{Symbol}, Any}}

_examples = Vector{Example}()
# _varorder = Dict{Symbol,Vector{Symbol}}()

# examples() = _examples
# example(s) = s=>_examples[s]

# varorders() = _varorder
# varorder(s) = _varorder[s]

# @example intcubicroot (1/4 + 3*r^2 == s && 1 + 4*x00+6*r^2 == 3*r+4*r^3+4*x)
# @example cubes        (n^3 == x && 1 + 3*n + 3*n^2 == y && 6 + 6*n == z)
# @example intsqrt2     (j == 2*k+1 && (1+j)^2 == 4*m)
# @example intsqrt1     (y00*2 + r == r^2 + 2*y)
# @example dijkstra     (r + q*y00 == r00)
# @example ex0          (x*y == 2*x)
# @example ex1          (a == b^2)
# @example ex2          (1 + 2*a == c && 4*b == (c-1)^2)
# @example ex3          (1 + 2*a == c && b + c == 1 + s && c*(c+2) == 3 + 4*s)


# @varorder intcubicroot x s r
# @varorder cubes        x y z n
# @varorder intsqrt1     y r
# @varorder intsqrt2     k j m
# @varorder dijkstra     x r q y
# @varorder ex1          a b

# Double
# x, y = 0, 1
# while true
#     x = 2x
#     y = 1/2 y + 1
# end
# @example double1 (x*y == 2x)
# @varorder double1 x y

# @example double2 (x == 2y)
# @varorder double2 x y

# Square
# a, b = 0, 0
# while true
#     a = a + 2b + 1
#     b = b + 1
# end
push!(_examples, Example((
    :square,
    @invariant(a == b^2),
    [:a, :b],
    Dict()
)))

# Sum1
# a, b, c = 0, 0, 1
# while true
#     a = a + 1
#     b = b + c
#     c = c + 2
# end
push!(_examples, Example((
    :sum1,
    @invariant(1 + 2a == c && 4b == (c-1)^2),
    [:a, :b, :c],
    Dict()
)))

# Sum2
# a, b, c, s = 0, 0, 1, 0
# while true
#     a = a + 1
#     b = b + c
#     c = c + 2
#     s = s + 2a + 1
# end
# @example sum2 (1 + 2a == c && b + c == 1 + s && c*(c+2) == 3 + 4s)
# @varorder sum2 s a b c

# eucliddiv
# r, q = x, 0
# while true
#     r = r - y
#     q = q + 1
# end
push!(_examples, Example((
    :eucliddiv,
    @invariant(x(0) == y(0)*q(n) + r(n)),
    [:r, :q, :x, :y],
    Dict(:params=>[:x, :y])
)))

# Integer Square Root - version 1
# k, j, m = 0, 1, 1
# while m<=n
#     k = k + 1
#     j = j + 2
#     m = m + j
# end
# @example intsqrt1 (j == 1 + 2k && (j+1)^2 == 4m)
# @varorder intsqrt1 m k j

# Integer Square Root - version 2
# y, r = 1/2*a, 0
# while true
#     y = y - r
#     r = r + 1
# end
# @example intsqrt2 (a00 + r == r^2 + 2y)
# @varorder intsqrt2 y r a

# Integer Cubic Root
# x, r, s = a, 1, 13/4
# while true
#     x = x-s
#     s = s + 6r + 3
#     r = r + 1
# end
# @example intcbrt (1/4 + 3r^2 == s && 1 + 4*a00 + 6r^2 == 3r + 4r^3 + 4x)
# @varorder intcbrt x s r a

# Consecutive Cubes
# n, x, y, z = 0, 0, 1, 6
# while true
#     x = x + y
#     y = y + z
#     z = z + 6
#     n = n + 1
# end
push!(_examples, Example((
    :cubes,
    @invariant(n^3 == x && 1 + 3n + 3n^2 == y && 6 + 6n == z),
    [:x, :y, :z, :n],
    Dict()
)))

# Petter 1
# x, y = 0, 0
# while true
#     x = x + y^1
#     y = y + 1
# end
# @example petter1 (y^2 == 2*x+y)
# @varorder petter1 x y

# Petter 2
# x, y = 0, 0
# while true
#     x = x + y^2
#     y = y + 1
# end
# 6 x == y * (-1 + 3 y - 2 y^2)

# Petter 3
# x, y = 0, 0
# while true
#     x = x + y^3
#     y = y + 1
# end
# 4 x - (-1 + y)^2 y^2

# Add (https://rise4fun.com/Dafny/Add)
# r = x
# n = y
# while n != 0
#     r = r + 1
#     n = n - 1
# end
push!(_examples, Example((
    :add1,
    @invariant(r(m) == x(0)+y(0)-n(m)),
    [:r, :n, :x, :y],
    Dict(:params=>[:x, :y])
)))

# r = 2x
# n = y
# while n != 0
#     r = r + 1
#     n = n - 1
# end
# @example add2 (r == 2*x00+y00-n)
# @varorder add2 r n x y

# q^4 + 2 * q^3 * r + r^4 == 1 + q^2*r^2 + 2*q*r^3

# ------------------------------------------------------------------------------

function report3(examples::Vector{Example}; solvers=[Yices,Z3], timeout=2, maxsol=1, shapes=[UnitUpperTriangular, UpperTriangular, FullSymbolic])
    progress = ProgressUnknown("Instances completed:")
    df = DataFrame(Solver = Type{<:NLSolver}[], Instance = Any[], Shape = MatrixShape[], Status = NLStatus[], Elapsed = TimePeriod[], Result = Union{RecSystem,Nothing}[])
    for ex in examples
        for shape in shapes
            strat = strategy_fixed2(ex.inv, copy(ex.vars), shape, [length(ex.vars)+1]; constone=true, ex.kwargs...)
            for solver in solvers
                sols = solutions(strat; solver=solver, timeout=timeout, maxsol=maxsol)
                for res in sols
                    push!(df, (solver, ex.name, shape, res.status, res.elapsed, res.recsystem))
                    next!(progress)
                end
            end
        end
    end
    finish!(progress)
    df
end

function wide(df)
    key = [:Instance, :Shape]
    tab = unstack(df, key, :Solver, :Elapsed)
    z3 = unstack(tab, :Instance, :Shape, :Z3Solver)
    yices = unstack(tab, :Instance, :Shape, :YicesSolver)
    rename!(z3, 
        :UnitUpperTriangular => :Z3_UnitUpperTriangular, 
        :UpperTriangular     => :Z3_UpperTriangular,
        :FullSymbolic        => :Z3_FullSymbolic
    )
    rename!(yices, 
        :UnitUpperTriangular => :Yices_UnitUpperTriangular, 
        :UpperTriangular     => :Yices_UpperTriangular,
        :FullSymbolic        => :Yices_FullSymbolic
    )
    join(yices, z3, on = :Instance, makeunique = true)
end