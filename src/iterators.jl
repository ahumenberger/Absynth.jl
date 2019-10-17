import Base: iterate

struct ClosedForms
    rt::RecurrenceTemplate
    part
end

function iterate(cf::ClosedForms)
    p, next = iterate(cf.part)
    ClosedFormTemplate(cf.rt, p), next
end

function iterate(cf::ClosedForms, state)
    s = iterate(cf.part, state)
    s === nothing && return
    ClosedFormTemplate(cf.rt, first(s)), last(s)
end

closedforms(rt::RecurrenceTemplate) = ClosedForms(rt, partitions(size(rt)))

# ------------------------------------------------------------------------------

struct Models
    solver::NLSolver
    problem::SynthesisProblem
    maxsol::Number
    timeout::Int

    function Models(p::SynthesisProblem, solver::Type{<:NLSolver}, maxsol::Number, timeout::Int)
        @assert maxsol >= 1
        new(create_solver(p, solver), p, maxsol, timeout)
    end
end

models(p::SynthesisProblem; maxsol::Number=Inf, timeout::Int=10, solver::Type{<:NLSolver}=Z3) =
    Models(p, solver, maxsol, timeout)

iterate(ms::Models) = iterate(ms, 0)

function iterate(ms::Models, state)
    (state === nothing || state >= ms.maxsol) && return
    model, result = solve(ms.problem, ms.solver, timeout=ms.timeout)
    model === nothing && return result, nothing
    next_constraints!(ms.solver, ms.problem, model)
    result, state+1
end

function next_constraints!(s::NLSolver, sp::SynthesisProblem, m::NLModel)
    vs = [Symbol(string(v)) for v in body(sp) if !isconstant(v)]
    cs = Clause([Constraint{NEQ}(:($v - $(m[v]))) for v in vs])
    constraints!(s, ClauseSet(cs))
end