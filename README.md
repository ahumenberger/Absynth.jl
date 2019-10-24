# Absynth.jl
> Algebra-based synthesizer

Absynth is a Julia package for synthesizing loops from a given polynomial loop invariant.

## Quick start

```julia
julia> ] add https://github.com/ahumenberger/Absynth.jl
julia> using Absynth
```

Absynth makes use of SMT solving at its core. As such you should have an SMT solver like Z3 [1] or Yices [2] installed.

You can check if Absynth can find Z3 or Yices by trying to call the constructor of the solver, that is, `Z3()` or `Yices()`. If this does not throw an error, then Z3 and/or Yices are available.

Then we can create a loop invariant which is allowed to be a Boolean combination of polynomial equations.

```julia
julia> inv = @invariant a == b^2
```

The result of calling `synth` is in fact a first-order recurrence system.

```julia
julia> recsys = synth(inv, solver=Z3)
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


[1] https://github.com/Z3Prover/z3
[2] http://yices.csl.sri.com/
