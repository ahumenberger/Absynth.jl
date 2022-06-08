# Absynth.jl
> **A**lgebra-**b**ased loop **synth**esizer

Absynth is a Julia package for synthesizing loops from a given polynomial loop invariant.

## Quick start

```julia
julia> ] add Absynth
julia> using Absynth
```

Absynth makes use of SMT solving at its core. As such you should have an SMT solver like [Z3](https://github.com/Z3Prover/z3) or [Yices](http://yices.csl.sri.com/) installed.

You can check if Absynth can find Z3 or Yices by trying to call the constructor of the solver, that is, `Z3()` or `Yices()`. If this does not throw an error, then Z3 and/or Yices are available.

Then we can create a loop invariant which is allowed to be a Boolean combination of polynomial equations.

```julia
julia> I = @invariant a == b^2
```

The result of calling `synth` is in fact a first-order recurrence system.

```julia
julia> recsys = synth(I, solver=Z3Solver)
RecSystem of size 3:
  ⎛ a(n+1)  ⎞   ⎛ 1  2  1 ⎞⎛ a(n)  ⎞	⎛ a(0)  ⎞   ⎛ 1//16 ⎞
  ⎜ b(n+1)  ⎟ = ⎜ 0  1  1 ⎟⎜ b(n)  ⎟	⎜ b(0)  ⎟ = ⎜ -1//4 ⎟
  ⎝ _c(n+1) ⎠   ⎝ 0  0  1 ⎠⎝ _c(n) ⎠	⎝ _c(0) ⎠   ⎝ 1     ⎠
```

We turn the recurrence system into a loop by calling `loop(recsys)`.

```julia
julia> loop(recsys)
quote
    a = 1//16
    b = -1//4
    while true
        a = a + 2b + 1
        b = b + 1
    end
end
```

## Tutorial

We assume that you have already installed and loaded the `Absynth` package. You need to follow the details in this section if you want to run benchmarks in your own desired setting. 

1. Create an object of type Invariant:

```julia
julia> I = @invariant x == y^2
```

The invariant can also be a conjunction of conditions. For example `x == y^2 && y == z` is also a valid invariant. 

2. Create a template for the recurrence system of type RecTemplate:

```julia
julia> rec = RecTemplate([:x, :y], constant_one=true, shape=UnitUpperTriangular)
```

If you believe that your synthesized loop with affine updates would need more variables, you can add them here in the list. Otherwise, just enter the variables occured in your given invariant. 

The argument `constant_one` specifies whether a dimensino for the constant 1 should be added. 

The argument `shape` specifies which shape the corresponding coefficient matrix should be preset to. There are three following options for this:
  * `UnitUpperTriangular`
  * `UpperTriangular`
  * `FullSymbolic`

FullSymbolic puts no constraints on the matrix. 

In the publications, the three options above are referred to as UN, UP, and FU, respectively. 

After entering the command above, you should receive such outout:
```julia
julia> rec = RecTemplate([:x, :y], constant_one=true, shape=UnitUpperTriangular)
RecTemplate for some permutation σ of Any[:x, :y, 1]:
	⎛ σ(x)(n+1) ⎞   ⎛ 1  b12  b13 ⎞⎛ σ(x)(n) ⎞	⎛ σ(x)(0) ⎞   ⎛ a11 ⎞
	⎜ σ(y)(n+1) ⎟ = ⎜ 0    1  b23 ⎟⎜ σ(y)(n) ⎟	⎜ σ(y)(0) ⎟ = ⎜ a21 ⎟
	⎝ σ(1)(n+1) ⎠   ⎝ 0    0    1 ⎠⎝ σ(1)(n) ⎠	⎝ σ(1)(0) ⎠   ⎝   1 ⎠

```

3. Set concrete initial values for elements of the coefficient/initial values matrices (optional):
```julia
julia> rec.init[1] = 4
4

julia> rec
RecTemplate for some permutation σ of Any[:x, :y, 1]:
	⎛ σ(x)(n+1) ⎞   ⎛ 1  b12  b13 ⎞⎛ σ(x)(n) ⎞	⎛ σ(x)(0) ⎞   ⎛   4 ⎞
	⎜ σ(y)(n+1) ⎟ = ⎜ 0    1  b23 ⎟⎜ σ(y)(n) ⎟	⎜ σ(y)(0) ⎟ = ⎜ a21 ⎟
	⎝ σ(1)(n+1) ⎠   ⎝ 0    0    1 ⎠⎝ σ(1)(n) ⎠	⎝ σ(1)(0) ⎠   ⎝   1 ⎠

  # a11 is now replaced by 4. 


julia> rec.body[2, 3] = 7
7

julia> rec
RecTemplate for some permutation σ of Any[:x, :y, 1]:
	⎛ σ(x)(n+1) ⎞   ⎛ 1  b12  b13 ⎞⎛ σ(x)(n) ⎞	⎛ σ(x)(0) ⎞   ⎛   4 ⎞
	⎜ σ(y)(n+1) ⎟ = ⎜ 0    1    7 ⎟⎜ σ(y)(n) ⎟	⎜ σ(y)(0) ⎟ = ⎜ a21 ⎟
	⎝ σ(1)(n+1) ⎠   ⎝ 0    0    1 ⎠⎝ σ(1)(n) ⎠	⎝ σ(1)(0) ⎠   ⎝   1 ⎠


  # b23 is now replaced by 4. 
```


4. Setting a strategy:

A strategy specifies how the search space should be explored. In our algorithm, we iterate over the set of integer paritions of the size of the recurrence template. Within Absynth, we can either iterate all partitions with `AllPartitions(::Int)`. Furthermore, we can specify which variable permutations we want to consider for finding a solution. We can either try all permutations via `AllPermutations(::Vector{Symbol})` or a fixed set of permutations by specifying `FixedPermutations(::Vector{Symbol}...).` Note that trying different permutations becomes relevant when considering a recurrence template with preset values.

The suggested way for this step is use AllPermutations with all of the variables in your template. If all your variables are x and y, it would be something like this:

```julia
julia> strat = Strategy(I, rec, perms=AllPermutations([:x, :y]), parts=AllPartitions(3))
Strategy with all permutations of [:x, :y] and all integer partitions of 3
```

The number 3 in FixedPartitions, should be replaced by the number of the dimensions in your coefficients matrix that is number of variables + 1 (If constant 1 is included). 

5. Creating a model

The strategy is then given to the function models(::Strategy) which creates an iterator for the set of solutions the solver finds. Currently, there are 3 solves available:
  * `Z3Solver`
  * `Absynth.CFiniteSolver`

`Z3Solver` and `Absynth.CFiniteSolver` correspond to Z3* and Z3* + Alg2, respectively in the publications. 

```
julia> ms = models(strat; solver=Z3Solver, timeout=2, maxsol=1)
```

The keywords `timeout` and `maxsol` specify the timeout and the maximal number of solutions the iterator should provide for each constructed PCP

6. Get the first solution
```julia
julia> recsys = first(ms)
	⎛ x(n+1) ⎞   ⎛ 1  2  1 ⎞⎛ x(n) ⎞	⎛ x(0) ⎞   ⎛  0.0625 ⎞
	⎜ y(n+1) ⎟ = ⎜ 0  1  1 ⎟⎜ y(n) ⎟	⎜ y(0) ⎟ = ⎜ -0.25   ⎟
	⎝ 1(n+1) ⎠   ⎝ 0  0  1 ⎠⎝ 1(n) ⎠	⎝ 1(0) ⎠   ⎝  1      ⎠ 
```

## Publications

1. [Humenberger, A., Bjørner, N., Kovács, L. (2020). Algebra-Based Loop Synthesis. In: Dongol, B., Troubitsyna, E. (eds) Integrated Formal Methods. IFM 2020.](https://doi.org/10.1007/978-3-030-63461-2_24)

2. [Humenberger, A., Kovács, L. (2021). Algebra-Based Synthesis of Loops and Their Invariants (Invited Paper). In: Henglein, F., Shoham, S., Vizel, Y. (eds) Verification, Model Checking, and Abstract Interpretation. VMCAI 2021](https://doi.org/10.1007/978-3-030-67067-2_2)

3. [A Humenberger, D Amrollahi, N Bjørner, L Kovács - Formal Aspects of Computing, 2022](https://dl.acm.org/doi/abs/10.1145/3527458)
