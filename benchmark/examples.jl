export examples, example

const Example = NamedTuple{(:name, :inv, :vars, :kwargs),Tuple{Symbol, Invariant, Vector{Symbol}, Any}}

_examples = Dict{Symbol,Example}()

example!(x::Example) = push!(_examples, x.name=>x)
examples() = values(_examples) |> collect
example(s) = _examples[s]

# Double
# x, y = 0, 1
# while true
#     x = 2x
#     y = 1/2 y + 1
# end
example!(Example((
    :double1,
    @invariant(x*y == 2x),
    [:x, :y],
    Dict()
)))
example!(Example((
    :double2,
    @invariant(x == 2y),
    [:x, :y],
    Dict()
)))

# Square
# a, b = 0, 0
# while true
#     a = a + 2b + 1
#     b = b + 1
# end
example!(Example((
    :square,
    @invariant(a == b^2),
    [:a, :b],
    Dict()
)))

example!(Example((
    :dblsquare,
    @invariant(a == 2*b^2),
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
example!(Example((
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
example!(Example((
    :sum2,
    @invariant(1 + 2a == c && b + c == 1 + s && c*(c+2) == 3 + 4s),
    [:s, :a, :b, :c],
    Dict()
)))

# eucliddiv
# r, q = x, 0
# while true
#     r = r - y
#     q = q + 1
# end
example!(Example((
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
example!(Example((
    :intsqrt1,
    @invariant(j == 1 + 2k && (j+1)^2 == 4m),
    [:m, :k, :j],
    Dict()
)))

# Integer Square Root - version 2
# y, r = 1/2*a, 0
# while true
#     y = y - r
#     r = r + 1
# end
example!(Example((
    :intsqrt2,
    @invariant(a(0) + r == r^2 + 2y),
    [:y, :r, :a],
    Dict(:params=>[:a])
)))

# Integer Cubic Root
# x, r, s = a, 1, 13/4
# while true
#     x = x-s
#     s = s + 6r + 3
#     r = r + 1
# end
example!(Example((
    :intcbrt,
    @invariant(1/4 + 3r^2 == s && 1 + 4*a(0) + 6r^2 == 3r + 4r^3 + 4x),
    [:x, :s, :r, :a],
    Dict(:params=>[:a])
)))

# Consecutive Cubes
# n, x, y, z = 0, 0, 1, 6
# while true
#     x = x + y
#     y = y + z
#     z = z + 6
#     n = n + 1
# end
example!(Example((
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
example!(Example((
    :petter1,
    @invariant(y^2 == 2*x+y),
    [:x, :y],
    Dict()
)))

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
example!(Example((
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
example!(Example((
    :add2,
    @invariant(r(m) == 2*x(0)+y(0)-n(m)),
    [:r, :n, :x, :y],
    Dict(:params=>[:x, :y])
)))

# ------------------------------------------------------------------------------

function Base.run(examples::Vector{Example}; solvers=[Yices,Z3], timeout=2, maxsol=1, shapes=[UnitUpperTriangular, UpperTriangular, FullSymbolic])
    progress = ProgressUnknown("Instances completed:")
    df = DataFrame(Solver = Type{<:NLSolver}[], Instance = Any[], Shape = MatrixShape[], Status = NLStatus[], Elapsed = Any[], Result = Union{RecSystem,Nothing}[])
    for ex in examples
        for shape in shapes
            strat = strategy_fixed(ex.inv, copy(ex.vars), shape, [length(ex.vars)+1]; constone=true, ex.kwargs...)
            for solver in solvers
                sols = solutions(strat; solver=solver, timeout=timeout, maxsol=maxsol)
                for res in sols
                    push!(df, (solver, ex.name, shape, res.status, res.elapsed, res.recsystem))
                    # push!(df, (solver, ex.name, shape, res.status, res.status == NLSat.timeout ? "-" : res.elapsed, res.recsystem))
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