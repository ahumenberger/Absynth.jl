
to_assignments(xs::Vector, ys::Vector) = ["$x = $y" for (x,y) in zip(xs,ys)]
to_lines(xs::Vector{String}, indent::Int) = join(xs, "\n$(repeat("    ", indent))")
to_list(xs) = join(xs, ", ")


function Base.summary(io::IO, l::Loop)
    print(io, "Loop for loop invariants (")
    # print(io, join(string.(invariants(s)), ","))
    # print(io, ")")
end

# function show(io::IO, l::Loop)
#     print(io, """
#         $(to_lines(to_assignments(l.vars, l.init), 1))
#         while true
#             $(to_lines(to_assignments(l.vars, l.body*l.vars), 2))
#         end
#     """)
# end

function Base.show(io::IO, l::Loop)
    # compact = get(io, :compact, false)

    # if compact
        show(io, l.body)
    # else
        # print(io, """
        # $(to_list(l.info.vars)) = $(to_list(l.init))
        # while true
        #     $(to_list(l.info.vars)) = $(to_list(l.body*l.info.vars))
        # end
        # """)
    # end
end

function Base.show(io::IO, ::MIME"text/plain", m::Loop)
    println("Synthesized loop:")
    show(io, m)
end