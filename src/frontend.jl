
abstract type DynamicsMatrix end

FullMatrix(s::Int) = [mkpoly(mkvar("b$i$j")) for i in 1:s, j in 1:s]
UpperTriangular(s::Int) = [j>=i ? mkpoly(mkvar("b$i$j")) : mkpoly(0) for i in 1:s, j in 1:s]
UnitUpperTriangular(s::Int) = [j>i ? mkpoly(mkvar("b$i$j")) : i==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]
Companion(s::Int) = [i==s ? mkpoly(mkvar("b$i$j")) : i+1==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]

_add_const_one(M::Matrix) = _add_row_one(hcat(M, zeros(eltype(M), size(M, 1), 1)))

function _add_row_one(M::Matrix)
    T = eltype(M)
    M = vcat(M, zeros(T, 1, size(M, 2)))
    M[end,end] = one(T)
    M
end

function initmatrix(vars::Vector{Symbol}, params::Vector{Symbol})
    rows, cols = length(vars), length(params)+1
    params = [params; 1]
    A = fill(mkpoly(1), (rows,cols))

    for i in 1:rows, j in 1:cols
        u, v = vars[i], params[j]
        if u == v
            A[i,j] = j == findfirst(x->x==u, params) ? 1 : 0
        else
            A[i,j] = findfirst(x->x==u, params) === nothing ? mkvar("a$i$j") : 0
        end
    end
    A
end

function bodymatrix(s::Int, shape::Symbol)
    if shape == :Full
        FullMatrix(s)
    elseif shape == :UpperTriangular
        UpperTriangular(s)
    elseif shape == :UnitUpperTriangular
        UnitUpperTriangular(s)
    elseif shape == :Companion
        Companion(s)
    else
        error("Unknown matrix shape: $shape")
    end
end

struct RecurrenceTemplate
    vars::Vector{Symbol}
    params::Vector{Symbol}
    body::Matrix{<:Poly}
    init::Matrix{<:Poly}
end

function RecurrenceTemplate(vars::Vector{Symbol}; constone::Bool = false, matrix::Symbol = :Full, params::Vector{Symbol}=Symbol[])
    size = length(vars)

    B = bodymatrix(size, matrix)
    A = initmatrix(vars, params)

    if constone
        push!(vars, :cc)
        B = _add_const_one(B)
        A = _add_row_one(A)
    end
    
    RecurrenceTemplate(vars, params, B, A)
end

# ------------------------------------------------------------------------------

struct ClosedFormTemplate
    vars::Vector{Symbol}
    params::Vector{Symbol}
    multiplicities::Vector{Int}

    function ClosedFormTemplate(v::Vector{Symbol}, p::Vector{Symbol}, m::Vector{Int})
        @assert length(v) == sum(m) "The sum of multiplicites has to match the number of variables."
        new(v, p, m)
    end
end

ClosedFormTemplate(rt::RecurrenceTemplate, ms::Vector{Int}) = ClosedFormTemplate(rt.vars, rt.params, ms)

# ------------------------------------------------------------------------------

struct SynthesisProblem
    inv::Invariant
    rt::RecurrenceTemplate
    ct::ClosedFormTemplate

    function SynthesisProblem(inv::Invariant, rt::RecurrenceTemplate, ct::ClosedFormTemplate)
        @assert issubset(variables(inv), rt.vars)
        @assert rt.vars == ct.vars && rt.params == ct.params
        new(inv, rt, ct)
    end
end

# ------------------------------------------------------------------------------

function Base.summary(io::IO, rt::RecurrenceTemplate)
    compact = get(io, :compact, false)
    if compact
        print(io, "RecurrenceTemplate ($(size(rt.body, 1)))")
    else
        print(io, "RecurrenceTemplate of size $(size(rt.body, 1))")
    end
end

function Base.show(io::IO, ::MIME"text/plain", rt::RecurrenceTemplate)
    summary(io, rt)
    println(io, ":")
    init = rt.init * [map(mkvar, rt.params); 1]
    _print_recsystem(io, rt.vars, rt.body, init)
end