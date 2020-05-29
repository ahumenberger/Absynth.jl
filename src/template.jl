@enum MatrixShape FullSymbolic UpperTriangular UnitUpperTriangular Companion UserSpecific

_FullSymbolic(s::Int)        = [mkpoly(mkvar("b$i$j")) for i in 1:s, j in 1:s]
_UpperTriangular(s::Int)     = [j>=i ? mkpoly(mkvar("b$i$j")) : mkpoly(0) for i in 1:s, j in 1:s]
_UnitUpperTriangular(s::Int) = [j>i ? mkpoly(mkvar("b$i$j")) : i==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]
_Companion(s::Int)           = [i==s ? mkpoly(mkvar("b$i$j")) : i+1==j ? mkpoly(1) : mkpoly(0) for i in 1:s, j in 1:s]
_UserSpecific(s::Int)        = error("Should not be called")

function _add_const_one(M::Matrix)
    s = size(M, 1) + 1
    col = [mkpoly(mkvar("b$i$s")) for i in 1:s-1]
    _add_row_one(hcat(M, col))
end

function _add_row_one(M::Matrix)
    T = eltype(M)
    M = vcat(M, zeros(T, 1, size(M, 2)))
    M[end,end] = one(T)
    M
end

function initmatrix(vars::Vector{Symbol}, params::Vector{SymOrNum})
    rows, cols = length(vars), length(params)
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

function bodymatrix(s::Int, shape::MatrixShape)
    f = Meta.parse(string("_", shape))
    eval(:($f($s)))
end

# ------------------------------------------------------------------------------

struct RecTemplate
    vars::Vector{Symbol}
    params::Vector{SymOrNum}
    body::Matrix{<:Poly}
    init::Matrix{<:Poly}
end

function RecTemplate(vars::Vector{Symbol}; shape::MatrixShape=UnitUpperTriangular, constant_one::Bool=true, params::Vector{Symbol}=Symbol[])
    size = length(vars)
    params = SymOrNum[params; 1]

    B = bodymatrix(size, shape)
    A = initmatrix(vars, params)

    if constant_one
        push!(vars, CONST_ONE_SYM)
        B = _add_const_one(B)
        A = _add_row_one(A)
    end
    
    RecTemplate(vars, params, B, A)
end

variables(r::RecTemplate) = r.vars

has_constant_one(r::RecTemplate) = r.vars[end] == CONST_ONE_SYM

function Base.summary(io::IO, r::RecTemplate)
    compact = get(io, :compact, false)
    vars = [v == CONST_ONE_SYM ? 1 : v for v in r.vars]
    if compact
        print(io, "$(typeof(r)) for some permutation of ")
        print(io, vars)
    else
        print(io, "$(typeof(r)) for some permutation σ of ")
        print(io, vars)
    end
end

function Base.show(io::IO, r::RecTemplate)
    summary(io, r)
    compact = get(io, :compact, false)
    if !compact
        println(io, ":")
        _show(io, r)
    end
end


function _show(io::IO, r::RecTemplate)
    init = r.init * map(mkpoly, r.params)
    vars = [v == CONST_ONE_SYM ? "σ(1)" : "σ($v)" for v in r.vars]
    _print_recsystem(io, vars, r.body, init)
    # @time _print_rectemplate(io, vars, r.body, init)
end


lpar2(h::Int, d = "") = h == 1 ? "($(d)" : ["⎛$(d)"; fill("⎜$(d)", h - 2); "⎝$(d)"]
rpar2(h::Int, d = "") = h == 1 ? "$(d))" : ["$(d)⎞"; fill("$(d)⎟", h - 2); "$(d)⎠"]

space2(h::Int, sp = " ") = fill(sp, h)

function symstr2(h::Int, symbol::String)
    a = fill(" ", h)
    a[Int(ceil(h/2))] = "$(symbol)"
    a
end

function _print_rectemplate(io::IO, vars, body, init)
    h = size(body, 1)
    lstr, rstr = lpar2(h), rpar2(h, "")
    eq = symstr2(h, "=")

    # lc = "\u2099"
    # lp, rp, plus = "", "", "\u208A"
    # zero, one = "\u2080", "\u2081"

    lc = "n"
    lp, rp, plus = "(", ")", "+" 
    zero, one = "0", "1"

    vars0 = ["$v$lp$zero$rp" for v in vars]
    vars1 = ["$v$lp$lc$rp" for v in vars]
    vars2 = ["$v$lp$lc$plus$one$rp" for v in vars]

    body = map(prettify_number, body)
    init = map(prettify_number, init)
    # add extra column such that all rows have equal length
    # body = hcat(body, fill(nothing, size(body, 1)))
    # init = hcat(init, fill(nothing, size(init, 1)))
    # body = sprint(Base.print_matrix, body)
    # init = sprint(Base.print_matrix, init)
    # body = Base.replace(body, "  $nothing" => "")
    # init = Base.replace(init, "  $nothing" => "")

    x = hcat(space2(h, " "), lstr, vars2, rstr, eq, lstr, body, rstr, lstr, vars1, rstr, space2(h, "    "), lstr, vars0, rstr, eq, lstr, init, rstr, space2(h, ""))
    str = sprint((args...)->Base.print_matrix(args...; ), x)
    str = Base.replace(str, "\""=>"")
    str = Base.replace(str, " ⎛ "=>"⎛")
    str = Base.replace(str, " ⎜ "=>"⎜")
    str = Base.replace(str, " ⎝ "=>"⎝")
    str = Base.replace(str, " ⎞ "=>"⎞")
    str = Base.replace(str, " ⎟ "=>"⎟")
    str = Base.replace(str, " ⎠ "=>"⎠")

    print(io, str)
end