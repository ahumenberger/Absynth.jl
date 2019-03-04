

function Base.summary(io::IO, t::LoopTemplate)
    print(io, "$(typeof(t)) with loop variables (")
    print(io, join(string.(vars(t)), ","))
    print(io, ") and unknowns (")
    print(io, join(string.(keys(args(t))), ","))
    print(io, ")")
end

function Base.show(io::IO, t::LoopTemplate)
    Base.summary(io, t)
    # printstyled(io, t, bold = true, color = :green)
    d = Dict{Symbol,Symbol}(v => gensym() for v in keys(args(t)))
    block = Expr(:block, body(t)...)
    for (k, v) in d
        block = MacroTools.replace(block, k, v)
    end

    println(io, ":")
    str = sprint(show, block)
    for (k, v) in d
        iob = IOBuffer()
        printstyled(IOContext(iob, :color => true), k, bold=true, color=:magenta)
        s = String(take!(iob))
        str = replace(str, string(v) => s)
    end
    str = replace(str, "quote" => "  while ...")
    str = replace(str, "end" => "  end")
    print(io, str)
end

function Base.summary(io::IO, s::Synthesizer)
    print(io, "Synthesizer for loop invariants (")
    print(io, join(string.(invariants(s)), ","))
    print(io, ")")
end

function Base.show(io::IO, s::Synthesizer)
    Base.summary(io, s)
end