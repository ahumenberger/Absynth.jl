

function Base.summary(io::IO, t::LoopTemplate)
    print(io, "$(typeof(t)) with loop variables (")
    print(io, join(string.(vars(t)), ","))
    print(io, ") and unknowns (")
    print(io, join(string.(args(t)), ","))
    print(io, ")")
end

function replaceexpr(ex::Expr, d::Pair...)
    for (k, v) in d
        ex = MacroTools.replace(ex, k, v)
    end
    ex
end

function strstyled(ex::Vector{Expr}, vars::Vector{Symbol}, vals::Dict{Symbol,CoeffType})
    d = Dict{Symbol,Symbol}(v=>gensym() for v in vars)
    block = Expr(:block, ex...)
    block = replaceexpr(block, d...)

    str = sprint(show, block)
    for (k, v) in d
        iob = IOBuffer()
        vstr = k == vals[k] ? "$(k)" : "$(k):$(vals[k])"
        printstyled(IOContext(iob, :color => true), vstr, bold=true, color=:magenta)
        s = String(take!(iob))
        str = replace(str, string(v) => s)
    end
    str
end

function Base.show(io::IO, t::LoopTemplate)
    Base.summary(io, t)
    println(io, ":")
    
    istr = strstyled(initexpr(t), collect(keys(initvalues(t))), initvalues(t))
    istr = replace(istr, "quote" => "")
    istr = replace(istr, "end" => "")
    istr = replace(istr, "  " => " ")
    print(io, istr)

    bstr = strstyled(bodyexpr(t), collect(args(t)), argvalues(t))
    bstr = replace(bstr, "quote" => "  while ...")
    bstr = replace(bstr, "end" => "  end")
    print(io, bstr)
end

function Base.summary(io::IO, s::Synthesizer)
    print(io, "Synthesizer for loop invariants (")
    print(io, join(string.(invariants(s)), ","))
    print(io, ")")
end

function Base.show(io::IO, s::Synthesizer)
    Base.summary(io, s)
end