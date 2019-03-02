module Absynth

using MacroTools

export @template, LoopTemplate, loop

# ------------------------------------------------------------------------------

struct LoopTemplate
    name::Symbol
    args::Vector{Symbol}
    body::Vector{Expr}
end

function (t::LoopTemplate)(vals::Union{Int,Rational}...)
    @assert length(vals) <= length(t.args) "Too many arguments"
    body = t.body
    for (i, v) in enumerate(vals)
        body = [MacroTools.replace(x, t.args[i], v) for x in body]
    end
    LoopTemplate(t.name, t.args[length(vals)+1:end], body)
end

function loop(t::LoopTemplate; iterations::Int = 10)
    quote
        for _ in 1:$iterations
            $(t.body...)
        end
    end
end

# ------------------------------------------------------------------------------

struct Synthesizer
    tmpl::LoopTemplate
    inv::Expr
    cstr::Vector{Expr}
end

Synthesizer(tmpl::LoopTemplate, inv::Expr) = Synthesizer(tmpl, inv, Expr[])

template(s::Synthesizer) = s.tmpl
constraints(s::Synthesizer) = s.cstr

function constraint!(s::Synthesizer, c::Expr)
    push!(s.cstr, c)
    return s
end

function synth(s::Synthesizer)

end

# ------------------------------------------------------------------------------

macro template(input)

    @capture(input, name_(args__) = begin assignments__ end)

    tname = [name]

    @info "" tname args assignments

    return esc(:($name = LoopTemplate($(tname)..., $(args), $(assignments))))
end


@template freire(a, b) = begin
    x = x + a
    y = y + b
end

s = Synthesizer(freire, :(x - y == 0))
constraint!(s, :(b > 0))
synth(s)

end # module
