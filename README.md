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

## Publications

1. [Humenberger, A., Bjørner, N., Kovács, L. (2020). Algebra-Based Loop Synthesis. In: Dongol, B., Troubitsyna, E. (eds) Integrated Formal Methods. IFM 2020.](https://doi.org/10.1007/978-3-030-63461-2_24)

2. [Humenberger, A., Kovács, L. (2021). Algebra-Based Synthesis of Loops and Their Invariants (Invited Paper). In: Henglein, F., Shoham, S., Vizel, Y. (eds) Verification, Model Checking, and Abstract Interpretation. VMCAI 2021](https://doi.org/10.1007/978-3-030-67067-2_2)

3. [A Humenberger, D Amrollahi, N Bjørner, L Kovács - Formal Aspects of Computing, 2022](https://dl.acm.org/doi/abs/10.1145/3527458)
