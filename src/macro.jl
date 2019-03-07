export @template, @generictemplate, @synth

    # @template freire(a, b) = begin
    #     x = x + a
    #     y = y + b
    # end
macro template(input)
    @capture(input, name_(args__) = begin assignments__ end)

    tname = [name]
    args = Dict{Any,Any}(map(x -> MacroTools.splitarg(x)[1:2], args))
    # set default variable type to Rational
    replace!(args) do kv
        last(kv) == :Any ? first(kv) => Rational{Int} : first(kv) => eval(last(kv))
    end
    args = convert(Dict{Symbol,Type}, args)

    return esc(:($name = LoopTemplate($(tname)..., $(args), convert(Vector{Expr}, $(assignments)))))
end

"""
    @generictemplate tmpl vars...

Create a generic loop template with name `tmpl` and the variables in `vars`.

# Examples
```julia-repl
julia> @generictemplate tmpl1 x y z
LoopTemplate with loop variables (y,z,x) and unknowns (a33,a11,a55,a22,a44,a66):

  y = y00
  z = z00
  x = x00
  while ...
    x = x + a11 * y + a22 * z + a33
    y = y + a44 * z + a55
    z = z + a66
  end
```
"""
macro generictemplate(name, vars...)
    esc(quote
        count = 0
        args = Dict{Symbol,Type}()
        function inc()
            global count += 1
            s = Symbol("a$count$count")
            push!(args, s=>Rational{Int})
            s
        end
        body = Expr[]
        for (i,v) in enumerate($vars)
            prev = [Expr(:call, :(*), inc(), $(vars)[j]) for j in i+1:length($vars)]
            ex = Expr(:(=), v, Expr(:call, :(+), v, prev..., inc()))
            push!(body, ex)
        end
        $name = LoopTemplate(:test, args, body)
    end)
end

function splitformula(expr)
    if @capture(expr, e1_ && e2_)
        return [[e1]; splitformula(e2)]
    end
    return [expr]
end

"""
    @synth tmpl inv [cstr] <keyword arguments>

Synthesize a loop for a given loop template `tmpl` satisfying the loop 
invariant `inv` and constraints `cstr`.

# Arguments
- `tmpl`: the name of the loop template.
- `inv`: a list of equality invariant separated by &&.
- `cstr`: a list of equality and inequality constraints separated by &&.
- `solver::Absynth.NLSolver=T`: the solver which should be used to solve the constraints.
- `timeout::Int=seconds`: the time limit for the solver.

# Examples
```julia-repl
julia> @generictemplate tmpl1 x y z
LoopTemplate with loop variables (y,z,x) and unknowns (a33,a11,a55,a22,a44,a66):

  y = y00
  z = z00
  x = x00
  while ...
    x = x + a11 * y + a22 * z + a33
    y = y + a44 * z + a55
    z = z + a66
  end

julia> @synth tmpl1 (x == y && y == z) (a66 > 1 && x00 > 1) solver=Absynth.Z3Solver timeout=10
LoopTemplate with loop variables (y,z,x) and unknowns (a33,a11,a55,a22,a44,a66):

  y = y00:2
  z = z00:2
  x = x00:2
  while ...
    x = x + a11:0 * y + a22:0 * z + a33:6
    y = y + a44:0 * z + a55:6
    z = z + a66:6
  end
```
"""
macro synth(args...)
    nargs = length(args)
    @assert nargs >= 2 "Missing arguments"
    tmpl = args[1]
    invariants = Vector{Expr}(splitformula(args[2]))
    constraints = nargs >= 3 ? Vector{Expr}(splitformula(args[3])) : []
    kwargs = collect(args[4:end])
    @debug "Parsed macro input" tmpl invariants constraints kwargs
    
    esc(quote
        s = Synthesizer($tmpl)
        invariants!(s, $invariants...)
        constraints!(s, $constraints...)
        solve(s; $(kwargs...))
    end)
end

