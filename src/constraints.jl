
import SymEngine.Basic
import SymPy.Sym

SymPy.Sym(x::Basic) = sympify(string(x))
SymEngine.Basic(x::SymPy.Sym) = Basic(string(x))

# if SymEngine.libversion < VersionNumber(0,4)
    function coeffs(ex::Basic, x::Basic)
        Basic.(sympy.Poly(Sym(ex), Sym(x)).coeffs())
    end
# else
#     function coeffs(ex::Basic, x::Basic)
#         d = degree(ex, x)
#         [coeff(ex, x, i) for i in d:-1:0]
#     end
# end

function degree(ex::Basic, x::Basic)
    convert(Int, SymPy.degree(Sym(ex), gen=Sym(x)))
end

function simplify(x::Basic)
    Basic(SymPy.simplify(Sym(x)))
end

isconstant(x::Basic) = isempty(SymEngine.free_symbols(x))

# ------------------------------------------------------------------------------

function dynamicsmatrix(size::Int, shape::Symbol)
    T = Basic
    if shape == :F
        # full
        B = [T("b$i$j") for i in 1:size, j in 1:size]
    elseif shape == :U
        # upper triangular
        B = [j>=i ? T("b$i$j") : zero(T) for i in 1:size, j in 1:size]
    elseif shape == :UT
        # unitriangular
        B = [j>i ? T("b$i$j") : i==j ? one(T) : zero(T) for i in 1:size, j in 1:size]
    end
    B
end

# function synth(::Type{T}, invs::Vector{Expr}) where {T<:NLSolver}
#     ps = map(Basic, invs)
#     fs = SymEngine.free_symbols(ps)
#     filter!(!isinitvar, fs)

#     dims = length(fs)
#     B = dynamicsmatrix(dims, :F)
#     for ms in reverse(collect(partitions(dims)))
#         @info "Multiplicities" ms
#         varmap, cstr = constraints(B, ps, ms)
#         # @info "" ideal(B, p, ms)

#         solver = T()
#         NLSat.variables!(solver, varmap)
#         NLSat.constraints!(solver, cstr)
#         status, model = NLSat.solve(solver)
#         @info "NL result" status model
#         if status == NLSat.sat
#             sol = [model[Symbol(string(b))] for b in B]
#             ivec = [model[Symbol(string(b))] for b in initvec(size(B, 1))]
#             @info "Solution found for partitioning $ms" sol ivec
#             return Loop(fs, ivec, sol)
#         else
#             @info "No solution found for partitioning $ms"
#         end
#     end
# end

initvar(s::T) where {T<:Union{Symbol,Basic}} = T("$(string(s))00")
isinitvar(s::Union{Symbol,Basic}) = endswith(string(s), "00")

# ------------------------------------------------------------------------------

to_expr(xs::Vector{Basic}) = map(x->convert(Expr, x), xs)

eq(x::Basic, y::Basic=zero(Basic)) = Expr(:call, :(==), convert(Expr, x), convert(Expr, y))
ineq(x::Basic, y::Basic=zero(Basic)) = Expr(:call, :(!=), convert(Expr, x), convert(Expr, y))

gensym_unhashed(s::Symbol) = Symbol(replace(string(gensym(s)), "#"=>""))

# ------------------------------------------------------------------------------

function raw_constraints(B::Matrix{Basic}, invs::Vector{Basic}, ms::Vector{Int})
    t = length(ms)
    rs = symroot(t)
    lc = Basic("n")
    cfs = cforms(size(B, 1), rs, ms, lc, one(Basic))
    fs = SymEngine.free_symbols(invs)
    d = Dict(zip(fs, cfs))
    ps = [SymEngine.subs(p, d...) for p in invs]

    # Equality constraints
    cscforms = cstr_cforms(B, rs, ms)
    csinit = cstr_init(B, rs, ms)
    csroots = cstr_roots(B, rs)
    csrel = [cstr_algrel(p, rs, lc) for p in ps]
    equalities = [collect(Iterators.flatten(cscforms)); csinit; csroots; collect(Iterators.flatten(csrel))]
    @debug "Equality constraints" cscforms csinit csroots csrel

    # Inequality constraints
    csnonconst = cstr_nonconstant(B)
    csdistinct = cstr_distinct(rs)
    inequalities = [csnonconst; csdistinct]
    @debug "Inequality constraints" csnonconst csdistinct

    cs = Iterators.flatten(symconst(i, j, size(B, 1)) for i in 1:t for j in 1:ms[i]) |> collect
    bs = Iterators.flatten(B) |> collect
    vars = [cs; rs]
    varmap = convert(Dict{Symbol,Type}, Dict(Symbol(string(v))=>AlgebraicNumber for v in vars))
    for b in [bs; initvec(size(B, 1))]
        push!(varmap, Symbol(string(b))=>AlgebraicNumber)
    end
    @debug "Variables" varmap

    varmap, equalities, inequalities
end

function constraints(B::Matrix{Basic}, inv::Vector{Basic}, ms::Vector{Int})
    varmap, equalities, inequalities = raw_constraints(B, inv, ms)
    varmap, [map(eq, equalities); map(ineq, inequalities)]
end

function ideal(B::Matrix{Basic}, inv::Vector{Basic}, ms::Vector{Int})
    varmap, equalities, inequalities = raw_constraints(B, inv, ms)
    auxvars = [gensym_unhashed(:z) for _ in 1:length(inequalities)]
    ineqs = [x*Basic(z) - 1 for (x,z) in zip(inequalities, auxvars)]
    for v in auxvars
        push!(varmap, v=>AlgebraicNumber)
    end
    R, _ = PolynomialRing(QQ, string.(keys(varmap)))
    gens = spoly{Singular.n_Q}[R(convert(Expr, p)) for p in [equalities; ineqs]]
    I = Ideal(R, gens)
    gb = std(I)
    varmap, [convert(Expr, x) for x in gb]
end

# ------------------------------------------------------------------------------

function cforms(varcnt::Int, rs::Vector{Basic}, ms::Vector{Int}, lc::Basic, exp::Basic=lc)
    t = length(rs)
    sum(symconst(i, j, varcnt) * rs[i]^exp * lc^(j-1) for i in 1:t for j in 1:ms[i])
end

initvec(n::Int) = [Basic("v$i") for i in 1:n]
symconst(i::Int, j::Int, rows::Int) = reshape([Basic("c$i$j$k") for k in 1:rows], rows, 1)
symroot(n::Int) = [Basic("w$i") for i in 1:n]

# ------------------------------------------------------------------------------

"Generate constraints describing the relationship between entries of B and the closed forms."
function cstr_cforms(B::Matrix{Basic}, rs::Vector{Basic}, ms::Vector{Int})
    rows = size(B, 1)
    t = length(rs)
    [sum(binomial(k-1, j-1) * symconst(i, k, rows) * rs[i] for k in j:ms[i]) - B * symconst(i, j, rows) for i in 1:t for j in 1:ms[i]]
end

"Generate constraints defining the initial values."
function cstr_init(B::Matrix{Basic}, rs::Vector{Basic}, ms::Vector{Int})
    s = size(B, 1)
    ivec = initvec(s)
    cfs = cforms(s, rs, ms, zero(Basic))
    [v - c for (v, c) in zip(ivec, cfs)]
end

"Generate constraints ensuring that sequence is not constant, i.e. B*B*x0 != B*x0."
function cstr_nonconstant(B::Matrix{Basic})
    ivec = initvec(size(B, 1))
    B * B * ivec - B * ivec
end

LinearAlgebra.det(m::Matrix{Basic}) = det(convert(SymEngine.CDenseMatrix, m))

"Generate constraints ensuring that the root symbols are roots of the characteristic polynomial of B."
function cstr_roots(B::Matrix{Basic}, rs::Vector{Basic})
    λ = Basic("lbd")
    cpoly = det(B-UniformScaling(λ)) |> simplify
    cstr = [SymEngine.subs(cpoly, λ=>r) for r in rs]
    cstr
end

"Generate constraints ensuring that the elements of rs are distinct."
cstr_distinct(rs::Vector{Basic}) = [r1-r2 for (r1,r2) in combinations(rs, 2)]

# ------------------------------------------------------------------------------

"Generate constraints ensuring that p is an algebraic relation."
function cstr_algrel(p::Basic, rs::Vector{Basic}, lc::Basic)
    qs = destructpoly(p, lc)
    cs = Basic[]
    for (i, q) in enumerate(qs)
        ms, us = destructterm(q, rs)
        l = length(ms)
        if all(isone, ms)
            l = 1
        end
        c = [sum(m^j*u for (m,u) in zip(ms,us)) for j in 0:l-1]
        append!(cs, c)
    end
    cs
end

# ------------------------------------------------------------------------------

function destructpoly(p::Basic, lc::Basic)
    coeffs(p, lc)
end

function destructterm(p::Basic, rs::Vector{Basic})
    ms = Basic[]
    cs = Basic[]
    for term in get_args(SymEngine.expand(p))
        ds = [degree(term, r) for r in rs]
        m = prod(r^d for (r,d) in zip(rs,ds))
        c = term / m
        push!(ms, m)
        push!(cs, c)
    end
    # a, b = factor(ms, cs)
    # @info "destruct term" length(a) length(ms)
    factor(ms, cs)
end

function factor(ms::Vector{Basic}, us::Vector{Basic})
    map = Dict{Basic,Basic}()
    for (m,u) in zip(ms,us)
        if haskey(map, m)
            map[m] += u
        else
            map[m] = u
        end
    end
    keys(map), Base.values(map)
end


