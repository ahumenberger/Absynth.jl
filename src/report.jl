using DataFrames
using ProgressMeter

export wide

const InvSet = Vector{Expr}

function report(polys; solvers=[Yices,Z3], timeout=2, maxsol=1, shapes=[full, upper, uni])
    progress = ProgressUnknown("Instances completed:")
    df = DataFrame(Solver = Type{<:NLSolver}[], Instance = Any[], Shape = MatrixShape[], Roots = Vector{Int}[], Loop = Union{Loop,NLStatus}[], ElapsedSolve = TimePeriod[])
    for solver in solvers
        for invset in polys
            for shape in shapes
                name, inv = invset isa Pair ? invset : (invset, invset)
                solutions = synth(inv, solver=solver, timeout=timeout, maxsol=maxsol, shape=shape, perm=false)
                for s in solutions
                    push!(df, (solver, name, shape, s.info.ctx.multi, s.result, s.elapsed))
                    next!(progress)
                end
            end
        end
    end
    finish!(progress)
    df
end

function report2(polys; solvers=[Yices,Z3], timeout=2, maxsol=1, shapes=[uni, upper, full])
    progress = ProgressUnknown("Instances completed:")
    df = DataFrame(Solver = Type{<:NLSolver}[], Instance = Any[], Shape = MatrixShape[], Roots = Vector{Int}[], Loop = Union{Loop,NLStatus}[], ElapsedSolve = TimePeriod[])
    for solver in solvers
        for invset in polys
            name, inv = invset isa Pair ? invset : (invset, invset)
            syms = SymEngine.free_symbols(map(Basic, inv))
            xparams, xvars = filtervars(syms)
            filter!(x->x!=Basic("cc00"), xparams)
            # push!(xvars, Basic("cc"))
            xvars = varorder(name)
            for shape in shapes
                @info name shape
                solutions = synth(inv, solver=solver, timeout=timeout, maxsol=maxsol, shape=shape, perm=false, part=[[length(xvars)+1]], vars=xvars, params=xparams)
                for s in solutions
                    push!(df, (solver, name, shape, s.info.ctx.multi, s.result, s.elapsed))
                    next!(progress)
                end
            end
        end
    end
    finish!(progress)
    df
end

function wide(df)
    key = [:Instance,:Shape,:Roots]
    t1 = unstack(df, key, :Solver, :ElapsedSolve)
    t2 = unstack(df, key, :Solver, :Loop)
    join(t1, t2, on = key, makeunique = true)
end

function rerun(df::DataFrame, row::Int; timeout=2, maxsol=1)
    r = df[row, :]
    solutions = synth(r.Polys, solver=r.Solver, timeout=timeout, maxsol=maxsol, shape=r.Shape)
    for s in solutions
        display(s)
    end
end