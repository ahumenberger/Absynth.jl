
to_assignments(xs::Vector, ys::Vector) = ["$x = $y" for (x,y) in zip(xs,ys)]
to_lines(xs::Vector{String}, indent::Int) = join(xs, "\n$(repeat("    ", indent))")
to_list(xs) = join(xs, ", ")

# Base.show(io::IO, s::NLStatus) = print(io, lowercase(string(s)))

function Base.show(io::IO, l::Loop)
    compact = get(io, :compact, false)

    if compact
        show(io, l.body)
    else
        h = size(l.body, 1)
        lstr, rstr = lpar(h), rpar(h, " ")
        body = sprint(Base.print_matrix, l.body)
        init = sprint(Base.print_matrix, l.init)
        str = mergestr(space(h, "\t"), lstr, body, rstr, space(h, "\t"), lstr, init, rstr)
        print(io, str)
    end
end

function Base.show(io::IO, ::MIME"text/plain", m::Loop)
    println("Synthesized loop:")
    show(io, m)
end

lpar(h::Int, d = "") = h == 1 ? "($(d)" : join(["⎛$(d)"; fill("⎜$(d)", h-2); "⎝$(d)"], "\n")
rpar(h::Int, d = "") = h == 1 ? "$(d))" : join(["$(d)⎞"; fill("$(d)⎟", h-2); "$(d)⎠"], "\n")

space(h::Int, sp=" ") = join(fill(sp, h), "\n")

function mergestr(strings::String...)
    splits = split.(strings, "\n")
    rows = length(splits[1])
    cols = length(splits)
    matr = reshape(collect(Iterators.flatten(splits)), rows, cols)
    join([join(matr[i,:]) for i in 1:size(matr, 1)], "\n")
end

function Base.summary(io::IO, s::SynthResult) where {T}
    compact = get(io, :compact, false)
    res = typeof(s.result) == Loop ? NLSat.sat : s.result
    if compact
        print(io, "SynthResult ($(res))")
    else
        print(io, "SynthResult ($(res)) in $(s.elapsed)")
    end
end

Base.show(io::IO, s::SynthResult) = summary(io, s)

function Base.show(io::IO, ::MIME"text/plain", s::SynthResult)
    summary(io, s)
    if typeof(s.result) == Loop
        println(io, ":")
        show(io, s.result)
    end
end

Base.show(io::IO, ::MIME"text/plain", ::Iterators.Stateful{Absynth.MultiSynthesizer{<:NLSolver}, Any}) = 
    print(io, "Stateful Synthesizer")


Base.summary(io::IO, s::Synthesizer{T}) where {T} =
    print(io, "Synthesizer for $(s.polys)")
# Base.summary(io::IO, s::MultiSynthesizer{T}) where {T} =
#     print(io, "Synthesizer for $(s.synth.polys) and at most $(s.maxsol) solutions")

function Base.show(io::IO, s::Synthesizer{T}) where {T}
    compact = get(io, :compact, false)

    print(io, "Synthesizer for $(s.polys)")
    if !compact
        println(io, " with options:")
        println(io, "Solver\t: $(T)")
        println(io, "Vars\t: $(s.vars)")
        println(io, "Shape\t: $(s.shape)")
        println(io, "Timeout\t: $(s.timeout) s")
    end
end

function Base.show(io::IO, s::MultiSynthesizer{T}) where {T}
    compact = get(io, :compact, false)

    summary(io, s)

    # if compact
    #     println(io, " and at most $(s.maxsol) solutions")
    # else
    #     println(io, "Maxsol\t: $(s.maxsol)")
    # end
end

Base.show(io::IO, s::NLSolver) = print(io, typeof(s))