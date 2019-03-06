
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
# 2 + r - r^2 - 2*x
@template freire1(a,b,c) = begin
    x = x + a*r + b
    r = r + c
end

# while x-s > 0
#     x = x-s
#     s = s+6*r+3
#     r = r+1
# end
# 2 - 3*r^2 + s
# -8 + 3*r + 12*r^2 - 12*r^3 - 7*s + 6*r*s + 6*x
# 14 + 15*r - 6*r^2 + 8*s + 3*r*s + 6*r^2*s - 4*s^2 - 18*x - 18*r*x
# 50 + 70*r + 23*s + 22*r*s + 36*r^2*s - 19*s^2 - 2*r*s^2 - 60*x - 90*r*x - 36*r^2*x + 6*s*x
# 2 - 54*r + 72*r^2 + 216*r^3 + 39*s - 162*r*s - 36*r^2*s + 216*r^3*s + 51*s^2 - 108*r*s^2 - 36*r^2*s^2 + 16*s^3 - 108*x + 108*r*x - 432*r^3*x - 108*s*x + 216*r*s*x + 108*x^2
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
# 5 - 6*n + z
# -17 + 12*y + 6*z - z^2
# 174 - 108*x - 84*y - 6*z + 18*y*z + 7*z^2 - z^3
# 162 - 90*x - 48*y - 24*y^2 - 23*z + 18*x*z + 5*y*z - z^2 + y*z^2
# 133 - 72*x - 5*y - 18*x*y - 38*y^2 + 5*z + 3*x*z - 7*y*z - y^2*z - 6*z^2 + 3*x*z^2 + 3*y*z^2
# 236 - 324*x + 108*x^2 - 348*y + 216*x*y + 96*y^2 + 16*y^3 - 66*z + 36*x*z + 78*y*z - 36*x*y*z - 12*y^2*z + 29*z^2 - 18*x*z^2 - 10*y*z^2 - y^2*z^2 - 3*z^3 + 2*x*z^3 + y*z^3
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