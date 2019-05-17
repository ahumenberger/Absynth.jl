using DataFrames

function report()
    df = DataFrame(Solver = Type{<:NLSolver}[], Polys = Vector{Basic}[], Roots = Vector{Int}[], Loop = Loop[])
    solutions = synth(Yices, [:(x-y)], 2, 2)
    for s in solutions
        push!(df, (s.info.solver, s.info.polys, s.info.roots, s))
    end
    df
end