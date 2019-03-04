export @template, @synth

    # @template freire(a, b) = begin
    #     x = x + a
    #     y = y + b
    # end
macro template(input)
    @capture(input, name_(args__) = begin assignments__ end)

    tname = [name]
    args = Dict{Any,Any}(map(x -> MacroTools.splitarg(x)[1:2], args))
    # set default variable type to Rational
    replace!(args) do kv
        last(kv) == :Any ? first(kv) => Rational{Int} : first(kv) => eval(last(kv))
    end
    args = convert(Dict{Symbol,Type}, args)

    return esc(:($name = LoopTemplate($(tname)..., $(args), convert(Vector{Expr}, $(assignments)))))
end

function splitformula(expr)
    if @capture(expr, e1_ && e2_)
        return [[e1]; splitformula(e2)]
    end
    return [expr]
end

macro synth(tmpl, invs, cstr)
    invariants = Vector{Expr}(splitformula(invs))
    constraints = Vector{Expr}(splitformula(cstr))
    @debug "Parsed macro input" tmpl invariants constraints
    
    esc(quote
        s = Synthesizer($tmpl)
        invariants!(s, $invariants...)
        constraints!(s, $constraints...)
        solve(s)
    end)
end

