const Z3Expr = Z3.Expr

Tactic(s::String) = Z3.Tactic(main_ctx(), s)

function mk_solver()
    t = Tactic("simplify") & Tactic("propagate-values") & Tactic("solve-eqs") &
        Tactic("purify-arith") & Tactic("elim-term-ite") & Tactic("simplify") & 
        Tactic("tseitin-cnf") & Tactic("nlsat")
    Z3.mk_solver(t)
end

function Int(x::Z3.Expr)
    @assert is_int(x)
    get_numeral_int(x)
end
Rational{Int}(x::Z3.Expr) = Int(numerator(x)) // Int(denominator(x))

function parse_model(m::Model)
    nlmodel = Dict{Symbol, Rational{Int}}()
    for (k,v) in consts(m)
        sym = Symbol(string(k))
        if is_int(v)
            push!(nlmodel, sym=>Int(v))
        elseif is_algebraic(v)
            approx = String(get_decimal_string(v, 10))[1:end-1]
            @warn "Algebraic numbers not yet supported, got $(v), returning approximation $(approx)"
            push!(nlmodel, sym=>parse(BigFloat, approx))
        elseif is_real(v)
            push!(nlmodel, sym=>try_int(Rational{Int}(v)))
        end
    end
    @debug "" nlmodel
    nlmodel
end

# ------------------------------------------------------------------------------

Z3.CxxWrap.@cxxdereference function Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, ex::XExpr)
    t = postwalk(ex) do x
        if x isa Float64
            # if isinteger(x)
            #     convert(Int, x)
            # else
                y = rationalize(x)
                real_val(ctx, numerator(y), denominator(y))
            # end
        elseif x isa Rational
            real_val(ctx, numerator(y), denominator(y))
        elseif x isa Int
            real_val(ctx, x)
        elseif issymbol(x)
            get(vs, x, x)
        else
            x
        end
    end
    eval(t)
end

Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{EQ})  = Z3Expr(ctx, vs, c.poly) == 0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{NEQ}) = Z3Expr(ctx, vs, c.poly) != 0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{LT})  = Z3Expr(ctx, vs, c.poly) <  0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{LEQ}) = Z3Expr(ctx, vs, c.poly) <= 0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{GT})  = Z3Expr(ctx, vs, c.poly) >  0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Constraint{GEQ}) = Z3Expr(ctx, vs, c.poly) >= 0
Z3Expr(ctx::Context, vs::Dict{Symbol,Z3Expr}, c::Clause) =
    length(c) > 1 ? or([Z3Expr(ctx, vs, x) for x in c]) : Z3Expr(ctx, vs, first(c))