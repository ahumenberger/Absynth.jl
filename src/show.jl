
to_assignments(xs::Vector, ys::Vector) = ["$x = $y" for (x,y) in zip(xs,ys)]
to_lines(xs::Vector{String}, indent::Int) = join(xs, "\n$(repeat("    ", indent))")
to_list(xs) = join(xs, ", ")

Base.show(io::IO, s::NLStatus) = print(io, lowercase(string(s)))

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