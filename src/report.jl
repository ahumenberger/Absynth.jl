using DataFrames
using ProgressMeter

const InvSet = Vector{Expr}

function report(polys::Vector{InvSet}; solvers=[Yices,Z3], timeout=5, maxsol=3)
    p = Progress(length(polys)*length(solvers)*maxsol)
    df = DataFrame(Solver = Type{<:NLSolver}[], Polys = Vector{Basic}[], Roots = Vector{Int}[], Loop = Union{Loop,NLStatus}[])
    for solver in solvers
        for invset in polys
            solutions = synth(solver, invset, timeout, maxsol)
            for s in solutions
                push!(df, (s.info.solver, s.info.polys, s.info.roots, s.result))
                next!(p)
            end
        end
    end
    finish!(p)
    df
end