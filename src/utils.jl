gensym_unhashed(s::Symbol) = Symbol(Base.replace(string(gensym(s)), "#"=>""))

constraint_walk(f, expr) = postwalk(expr) do x
    @capture(x, p_ == 0) ? f(p) : x
end

function_walk(f, expr) = postwalk(expr) do x
    @capture(x, g_(a__)) && issymbol(g) ? f(g, a) : x
end

symbol_walk(f, ex) = postwalk(x -> issymbol(x) ? f(x) : x, ex)

atom_walk(f, x) = walk(x, x -> (@capture(x, y_(ys__)) && issymbol(y)) ? f(x) : atom_walk(f, x) , f)

issymbol(x) = x isa Symbol && Base.isidentifier(x)
isfunction(x) = @capture(x, s_(xs__)) && s isa Symbol && Base.isidentifier(s)

function symbols(x::Expr)
    ls = Symbol[]
    symbol_walk(x) do s
        push!(ls, s)
        s
    end
    unique(ls)
end