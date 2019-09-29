
export Invariant, variables
export preprocess_invariant

# abstract type Func end

# struct VarFunc <: Func
#     f::Symbol
#     var::Symbol
#     shift::Int
# end

# struct IntFunc <: Func
#     f::Symbol
#     arg::Int
# end

# struct Invariant
#     poly::Union{Symbol,Expr}
#     vmap::Dict{Symbol,Func}

#     function Invariant(ex::Expr)
#         d = Dict{Symbol,Func}()
#         res = MacroTools.postwalk(ex) do x
#             if @capture(x, f_(args__)) && Base.isidentifier(f)
#                 @info "" x f args
#                 length(args) != 1 && error("Too many arguments in $x")
#                 var = gensym_unhashed(f)
#                 if args[1] isa Int
#                     fn = IntFunc(f, args[1])
#                 else
#                     poly = mkpoly(args[1])
#                     vars = variables(poly)
#                     length(vars) != 1 && error("Too many loop counters, got $vars")
#                     shift = poly - vars[1]
#                     fn = VarFunc(f, Symbol(string(vars[1])), shift)
#                 end
#                 push!(d, var=>fn)
#                 return var
#             end
#             x
#         end
#         new(res, d)
#     end
# end

issymbol(x) = x isa Symbol && Base.isidentifier(x)
symbols(f, ex) = postwalk(x -> issymbol(x) ? f(x) : x, ex)
isfunction(x) = @capture(x, s_(xs__)) && s isa Symbol && Base.isidentifier(s)
functions(f, ex) = postwalk(x -> isfunction(x) ? f(x) : x, ex)

function _checkfunc(x, xs)
    x in [:(<), :(<=), :(>), :(>=)] && error("Only Boolean combinations of equalities allowed, got $x")
    # if issymbol(x)
    #     symbols(xs[1]) do s
    #         s != :n && error("Only loop counter 'n' allowed")
    #     end
    # end
    :($x($(xs...)))
end

function _checksym(x, lc)
    issymbol(x) && x != lc && return :($x($lc))
    x
end

atomwalk(f, x) = walk(x, x -> (@capture(x, y_(ys__)) && issymbol(y)) ? f(x) : atomwalk(f, x) , f)

function preprocess_invariant(expr::Expr, lc::Symbol)
    atomwalk(expr) do ex
        @match ex begin
            x_ && y_ => :($x & $y)
            x_ || y_ => :($x | $y)
            x_ != 0  => :(~($x == 0))
            0 != x_  => :(~($x == 0))
            x_ != y_ => :(~($x-$y == 0))
            x_ == 0  => :($x == 0)
            0 == x_  => :($x == 0)
            x_ == y_ => :($x-$y == 0)
            x_(xs__) => _checkfunc(x, xs)
            _        => _checksym(ex, lc)
        end
    end
end

constraint_walk(f, expr) = postwalk(expr) do x
    @capture(x, p_ == 0) ? f(p) : x
end

function_walk(f, expr) = postwalk(expr) do x
    @capture(x, g_(a__)) && issymbol(g) ? f(g, a) : x
end

symbol_walk(f, ex) = postwalk(x -> issymbol(x) ? f(x) : x, ex)


function check_loop_counter(expr::Expr)
    lc = nothing
    function_walk(expr) do _, args
        length(args) != 1 && error("More than one argument, got $args")
        symbol_walk(args[1]) do s
            !isnothing(lc) && lc != s && error("More than one loop counter found, got ($lc, $s)")
            lc = s
        end
    end
    lc
end

# ------------------------------------------------------------------------------

struct Invariant
    x::Expr
    lc::Symbol
    function Invariant(x::Expr)
        lc = check_loop_counter(x)
        unique_lc = gensym_unhashed(isnothing(lc) ? :n : lc)
        x = replace(x, lc, unique_lc)
        new(preprocess_invariant(x, unique_lc), unique_lc)
    end
end

function variables(i::Invariant)
    ls = Symbol[]
    postwalk(i.x) do x
        if @capture(x, f_(_)) && issymbol(f)
            push!(ls, f)
        end
        x
    end
    unique(ls)
end

constraint_walk(f, i::Invariant) = constraint_walk(f, i.x)
function_walk(f, i::Invariant) = function_walk(f, i.x)

# ------------------------------------------------------------------------------

