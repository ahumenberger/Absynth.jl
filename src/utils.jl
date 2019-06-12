
splitformula(expr) = 
    @capture(expr, e1_ && e2_) ? [[e1]; splitformula(e2)] : [expr]
resolveequation(expr) = 
    @capture(expr, lhs_ == rhs_) ? :($lhs - $rhs) : @error "Only equalities allowed. Ignoring $expr"

parseformula(expr) = map(resolveequation, splitformula(expr))

export @synth

macro synth(ps, kwargs...)
    args = [esc(a) for a in kwargs]
    :(Iterators.Stateful(synth($(parseformula(ps)); $(args...))))
end
