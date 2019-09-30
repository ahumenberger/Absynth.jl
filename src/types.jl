
# export Invariant, variables
# export preprocess_invariant

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

function program_variables(i::Invariant)
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

