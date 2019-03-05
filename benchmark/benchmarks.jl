
using BenchmarkTools
using Absynth

macro sbench(suite, args...)
    esc(quote
        $suite[join(string.($args), " | ")] = @benchmarkable @synth $(args...)
    end)
end

@template freire(a, b) = begin
    x = x + a
    y = y + b
end

const group = BenchmarkGroup()

@sbench group freire (x == 3y) (b>0 && x_0>1)
@sbench group freire (x == 3y && x==y) (b>0 && x_0>1)

tune!(group)
results = run(group)

show(results)