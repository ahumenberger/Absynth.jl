
to_assignments(xs::Vector, ys::Vector) = ["$x = $y" for (x, y) in zip(xs, ys)]
to_lines(xs::Vector{String}, indent::Int) = join(xs, "\n$(repeat("    ", indent))")
to_list(xs) = join(xs, ", ")

# ------------------------------------------------------------------------------

lpar(h::Int, d = "") = h == 1 ? "($(d)" : join(["⎛$(d)"; fill("⎜$(d)", h - 2); "⎝$(d)"], "\n")
rpar(h::Int, d = "") = h == 1 ? "$(d))" : join(["$(d)⎞"; fill("$(d)⎟", h - 2); "$(d)⎠"], "\n")

space(h::Int, sp = " ") = join(fill(sp, h), "\n")

function symstr(h::Int, symbol::String)
    a = fill("   ", h)
    a[Int(ceil(h/2))] = " $(symbol) "
    return join(a, "\n")
end

function mergestr(strings::String...)
    splits = split.(strings, "\n")
    rows = length(splits[1])
    cols = length(splits)
    matr = reshape(collect(Iterators.flatten(splits)), rows, cols)
    join([join(matr[i,:]) for i in 1:size(matr, 1)], "\n")
end

# ------------------------------------------------------------------------------

function Base.summary(io::IO, l::Loop)
    compact = get(io, :compact, false)
    if compact
        print(io, "Loop ($(size(l.body, 1)))")
    else
        print(io, "Loop of size $(size(l.body, 1))")
    end
end

Base.show(io::IO, l::Loop) = summary(io, l)

function Base.show(io::IO, ::MIME"text/plain", l::Loop)
    summary(io, l)
    println(io, ":")
    h = size(l.body, 1)
    lstr, rstr = lpar(h), rpar(h, " ")
    eq = symstr(h, "=")

    lc = "\u2099"
    lp, rp, plus = "", "", "\u208A" 
    zero, one = "\u2080", "\u2081"

    # lc = "n"
    # lp, rp, plus = "(", ")", "+" 
    # zero, one = "0", "1"

    vars0 = replace(sprint(Base.print_matrix, map(x->string(x)*"$lp$zero$rp", l.vars)), "\""=>"")
    vars1 = replace(sprint(Base.print_matrix, map(x->string(x)*"$lp$lc$rp", l.vars)), "\""=>"")
    vars2 = replace(sprint(Base.print_matrix, map(x->string(x)*"$lp$lc$plus$one$rp", l.vars)), "\""=>"")
    body = sprint(Base.print_matrix, l.body)
    init = sprint(Base.print_matrix, l.init)

    lhs1 = (lstr, vars2, rstr)
    rhs1 = (lstr, body, rstr, lstr, vars1, rstr)

    lhs2 = (lstr, vars0, rstr)
    rhs2 = (lstr, init, rstr)
    str = mergestr(space(h, "\t"), lhs1..., eq, rhs1..., space(h, "\t"), lhs2..., eq, rhs2...)
    print(io, str)
end

# ------------------------------------------------------------------------------

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
        show(io, MIME("text/plain"), s.result)
    end
end

# ------------------------------------------------------------------------------

Base.show(io::IO, s::NLSolver) = print(io, typeof(s))

# ------------------------------------------------------------------------------

# Base.summary(io::IO, s::Synthesizer{T}) where {T} =
#     print(io, "Synthesizer for $(s.polys)")
# # Base.summary(io::IO, s::MultiSynthesizer{T}) where {T} =
# #     print(io, "Synthesizer for $(s.synth.polys) and at most $(s.maxsol) solutions")

# function Base.show(io::IO, s::Synthesizer{T}) where {T}
#     compact = get(io, :compact, false)

#     print(io, "Synthesizer for $(s.polys)")
#     if !compact
#         println(io, " with options:")
#         println(io, "Solver\t: $(T)")
#         println(io, "Vars\t: $(s.vars)")
#         println(io, "Shape\t: $(s.shape)")
#         println(io, "Timeout\t: $(s.timeout) s")
#     end
# end

# function Base.show(io::IO, s::MultiSynthesizer{T}) where {T}
#     compact = get(io, :compact, false)

#     summary(io, s)

#     # if compact
#     #     println(io, " and at most $(s.maxsol) solutions")
#     # else
#     #     println(io, "Maxsol\t: $(s.maxsol)")
#     # end
# end