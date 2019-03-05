
using BenchmarkTools
using Absynth

macro sbench(suite, args...)
    esc(quote
        $suite[join(string.($args), " | ")] = @benchmarkable @synth $(args...)
    end)
end

# while x>r
#     x = x-r
#     r = r+1
# end
@template freire1(a,b,c) = begin
    x = x + a*r + b
    r = r + c
end

# while x-s > 0
#     x = x-s
#     s = s+6*r+3
#     r = r+1
# end
@template freire2(a,b,c,d,e,f) = begin
    x = x + a*s + b*r + c
    s = s + d*r + e
    r = r + f
end

# while n<=N
#     n = n+1
#     x = x+y
#     y = y+z
#     z = z+6
# end
@template cohencu(a,b,c,d,e,f,g,h,i,j) = begin
    n = n + a
    x = x + b*n + c
    y = y + d*x + e*n + f
    z = z + g*y + h*x + i*n + j
end


const group = BenchmarkGroup()

@sbench group freire1 (x == 3y) (b>0 && x_0>1)
@sbench group freire1 (x == 3y && x==y) (b>0 && x_0>1)

tune!(group)
results = run(group)

show(results)