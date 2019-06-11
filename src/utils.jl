function splitformula(expr)
    if @capture(expr, e1_ && e2_)
        return [[e1]; splitformula(e2)]
    end
    return [expr]
end

export @synth

macro synth(ps, kwargs...)
    args = [esc(a) for a in kwargs]
    :(Iterators.Stateful(synth($(splitformula(ps)); $(args...))))
end
