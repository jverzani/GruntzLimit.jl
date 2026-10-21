# ---------------------------------------------------------------------------
# A front end: `limit` and `@limit` (not exported)
# ---------------------------------------------------------------------------
# the direction given to `limit`, as `gruntz_limit` takes it
function limit_dir(dir)
    dir in (:+, "+", '+', +) && return :+
    dir in (:-, "-", '-', -) && return :-
    dir in (:both, "both") && return :both
    throw(ArgumentError("dir must be :both, or :+ / :- (also given as +, \"+\", '+' or -, \"-\", '-'); " *
                        "got $(repr(dir))"))
end

"""
    GruntzLimit.limit(f, x => x0; dir = :both, kwargs...)

The limit of `f` as `x` tends to `x0`: a convenience front end to [`gruntz_cases`](@ref).

* `dir` is `:both` (the default: both one-sided limits must agree), or `:+` / `:-`, which
  may also be given as `+`, `"+"`, `'+'` and `-`, `"-"`, `'-'`.
* `kwargs` are passed on: `signs`, `build`, `lift`.

Returns the limit when it is the same for all values of the parameters, otherwise the
[`LimitCases`](@ref). Throws [`GruntzError`](@ref) when the limit does not exist or
cannot be computed for any value of the parameters.

```julia
julia> import GruntzLimit: limit

julia> limit(:(sin(x)/x), :x => 0)
1

julia> limit(:(1/x), :x => 0; dir = +)
Inf
```
"""
function limit(f, xx0::Pair; dir = :both, kwargs...)
    x, x0 = xx0
    cs = gruntz_cases(f, x, x0; dir = limit_dir(dir), kwargs...)
    (length(cs) == 1 && isempty(cs[1].first)) || return cs
    v = cs.vals[1]
    v isa GruntzError && throw(v)
    cs[1].second
end

"""
    GruntzLimit.@limit(f, x => x0)
    GruntzLimit.@limit(f, x => x0, dir)
    GruntzLimit.@limit(f, x => x0, [dir,] key = value...)

[`limit`](@ref GruntzLimit.limit) of the expression `f`, written without quoting: `f` is
taken as a Julia `Expr` in the variable `x`. Other names in `f` are parameters; use `\$v` to
put in the value of a variable `v`. The point `x0`, `dir` and the keyword values are
evaluated as usual.

```julia
julia> import GruntzLimit: @limit

julia> @limit(sin(x)/x, x => 0)
1

julia> @limit(1/x, x => 0, -)
-Inf

julia> @limit(x^a, x => Inf, signs = Dict(:a => :positive))
Inf
```
"""
macro limit(f, xx0, args...)
    (xx0 isa Expr && xx0.head === :call && length(xx0.args) == 3 &&
     xx0.args[1] === :(=>) && xx0.args[2] isa Symbol) ||
        throw(ArgumentError("@limit: the second argument must be `x => x0`, `x` a variable name"))
    x, x0 = xx0.args[2], xx0.args[3]
    kws = Any[]
    for (i, a) in enumerate(args)
        if a isa Expr && a.head === :(=) && a.args[1] isa Symbol
            push!(kws, Expr(:kw, a.args[1], esc(a.args[2])))
        elseif i == 1
            push!(kws, Expr(:kw, :dir, esc(a)))
        else
            throw(ArgumentError("@limit: after `x => x0`, only a direction and `key = value` " *
                                "arguments are allowed; got `$a`"))
        end
    end
    # quoting (not a QuoteNode) lets `$v` put in the value of `v`
    :(limit($(esc(Expr(:quote, f))), $(QuoteNode(x)) => $(esc(x0)); $(kws...)))
end
