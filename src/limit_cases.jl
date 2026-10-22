# ---------------------------------------------------------------------------
# The cases, as returned by `gruntz_cases`
# ---------------------------------------------------------------------------
"""
    CaseCondition(lhs, rel, rhs)

A condition `lhs rel rhs` on parameters, in a case of [`gruntz_cases`](@ref). `rel` is
one of `:<`, `:<=`, `:(==)`, `:!=`, `:>=`, `:>`; `lhs` and `rhs` are terms of the input's
type (made with `build`), or numbers.
"""
struct CaseCondition
    lhs::Any
    rel::Symbol
    rhs::Any
end
Base.show(io::IO, c::CaseCondition) = print(io, c.lhs, " ", c.rel, " ", c.rhs)

const REL_RANK = Dict(:< => 1, :<= => 2, :(==) => 3, :!= => 4, :>= => 5, :> => 6)

# the conditions of a case as text, a lower and an upper bound of the same term
# chained (0 < a < 1)
function show_conditions(conds::Vector{CaseCondition})
    isempty(conds) && return "always"
    parts = String[]
    used = falses(length(conds))
    for (i, c) in enumerate(conds)
        used[i] && continue
        j = c.rel in (:>, :>=) ? findfirst(k -> !used[k] && k != i && conds[k].rel in (:<, :<=) &&
                                                 isequal(conds[k].lhs, c.lhs), eachindex(conds)) : nothing
        if j === nothing
            push!(parts, string(c))
        else
            used[j] = true
            push!(parts, string(c.rhs, " ", flip(c.rel), " ", c.lhs, " ", conds[j].rel, " ", conds[j].rhs))
        end
        used[i] = true
    end
    join(parts, " && ")
end

# c rel 0, solved for a parameter it is linear in when there is one (a - b > 0 is
# shown as a > b, log(a) - 1 < 0 as a < exp(1), log(-a) - 1 < 0 as a > -exp(1))
function show_condition(bd::Builder, c::Sum, rel::Symbol)
    for (m, k) in sort!(collect(c.t); by = p -> p.first.key)
        (length(m.fs) == 1 && isone(m.fs[1].second)) || continue
        pw = param_of(m.fs[1].first)
        pw === nothing && continue
        p, how = pw
        r = subS(c, monoS(m, k))
        hasleaf(r, p.key) && continue
        rel2 = (k < 0) ⊻ (how === :neglog) ? flip(rel) : rel   # -p rel e^v is p flip(rel) -e^v
        return CaseCondition(user_value(bd, atomS(p)), rel2, user_value(bd, param_value(how, scaleS(r, -inv(k)))))
    end
    CaseCondition(user_value(bd, c), rel, 0)
end

"""
    LimitCases

The result of [`gruntz_cases`](@ref) (a public type, not exported): a vector of `conditions => limit` pairs, the
conditions a `Vector` of [`CaseCondition`](@ref)s that all hold in the case (empty when
the limit does not depend on the parameters). A limit is a value as returned by
[`gruntz_limit`](@ref), `:nolimit` when the limit does not exist, `:undefined` when the
expression is not defined for those parameters, or a [`GruntzError`](@ref) when the case
could not be computed.

A `LimitCases` is an `AbstractVector` of the pairs (`cs[2]`, `cs[end]`, `filter`, ...).
With values of the parameters, as pairs `parameter => value` or a `Dict`, calling it gives
the limit for those values (the case's limit with the values substituted), indexing gives
their case.

```julia
cs = gruntz_cases(:(x^(a - 2)), :x)
cs[end]          # CaseCondition[a > 2] => Inf
cs(:a => 3)      # Inf

cs = gruntz_cases(:((a^x + b^x)^(1/x)), :x)
cs(:a => 2, :b => 3)                  # 3
cs[:a => 2, :b => 3]                  # the case: CaseCondition[...] => :b
```
"""
struct LimitCases <: AbstractVector{Pair{Vector{CaseCondition},Any}}
    cases::Vector{Pair{Vector{CaseCondition},Any}}
    clist::Vector{Vector{Tuple{Sum,Symbol}}}   # each case's conditions, c rel 0
    ctx::Vector{Cond}                         # from `signs`
    sub::Dict{String,Sum}
    vals::Vector{Any}                         # each case's limit (Sum, Infinity, GruntzError)
    bd::Builder
end
Base.size(c::LimitCases) = size(c.cases)
Base.getindex(c::LimitCases, i::Int) = c.cases[i]
Base.IndexStyle(::Type{LimitCases}) = IndexLinear()

# whether c rel 0 holds for the parameter values `vals` (leaf key => Sum)
function holds_at(c::Sum, rel::Symbol, vals::Dict{String,Sum})
    v = try
        substS(c, vals)
    catch err
        err isa GruntzError || rethrow()
        return false                  # e.g. log of a negative value
    end
    sg = try
        csign(v)
    catch err
        err isa NeedSign || rethrow()
        free = [string(a.head) for m in keys(v.t) for (a, _) in m.fs if isparam(a)]
        throw(ArgumentError("give a value for `$(isempty(free) ? skey(v) : first(free))`"))
    end
    rel === :< ? sg < 0 : rel === :<= ? sg <= 0 : rel === :(==) ? sg == 0 :
    rel === :!= ? sg != 0 : rel === :>= ? sg >= 0 : sg > 0
end

# The index of the case whose conditions hold for the given values of the parameters
# (pairs `parameter => value`, parameters written as in `signs`, or a Dict). Throws an
# ArgumentError when a needed value is missing, or the values are outside the signs given.
findcase(cs::LimitCases, vals::AbstractDict) = findcase(cs, pairs(vals)...)
findcase(cs::LimitCases, vals::Pair...) = find_values(cs, vals)[1]
Base.getindex(cs::LimitCases, val::Pair, vals::Pair...) = cs.cases[findcase(cs, val, vals...)]
Base.getindex(cs::LimitCases, vals::AbstractDict) = cs.cases[findcase(cs, vals)]

# the index of the case for the values, and the values by leaf key
function find_values(cs::LimitCases, vals)
    d = Dict{String,Sum}()
    for (p, v) in vals
        a = single_atom(from_term(p))
        (a === nothing || a.kind !== :leaf) && throw(ArgumentError("`$p` is not a parameter"))
        c = from_term(v)
        ratconst(c) === nothing && numval_or_nothing(baseatom(c)) === nothing &&
            throw(ArgumentError("the value of `$p` must be a number, got $v"))
        d[a.key] = c
    end
    with_context(Cond[], Dict{String,Sum}(), false, WLEAF) do
        for (k, v) in cs.sub          # a parameter given as :zero in `signs` is substituted
            haskey(d, k) && !holds_at(subS(d[k], substS(v, d)), :(==), Dict{String,Sum}()) &&
                throw(ArgumentError("the values are outside the signs given"))
        end
        all(cd -> holds_at(cd.c, cd.rel, d), cs.ctx) ||
            throw(ArgumentError("the values are outside the signs given"))
        i = findfirst(clist -> all(((c, rel),) -> holds_at(c, rel, d), clist), cs.clist)
        i === nothing && throw(ArgumentError("no case applies to these values"))
        i, d
    end
end
function (cs::LimitCases)(vals::Pair...)
    i, d = find_values(cs, vals)
    v = cs.vals[i]
    v isa Sum || return cs.cases[i].second
    user_value(cs.bd, with_context(() -> substS(substS(v, cs.sub), d), Cond[], Dict{String,Sum}(), false, WLEAF))
end
(cs::LimitCases)(vals::AbstractDict) = cs(pairs(vals)...)

function Base.show(io::IO, ::MIME"text/plain", c::LimitCases)
    n = length(c.cases)
    print(io, "LimitCases with ", n, n == 1 ? " case:" : " cases:")
    for (conds, v) in c.cases
        print(io, "\n  ", show_conditions(conds), "  =>  ")
        v isa GruntzError ? print(io, "not computed (", v.msg, ")") : print(io, v)
    end
end

"""
    gruntz_cases(f, x, x0 = Inf; dir = :+, build = nothing, lift = nothing, signs = ())

The limit of `f` as in [`gruntz_limit`](@ref), for each case of the free parameters
in it. Where the limit depends on the sign of a constant with
parameters, such as `a - 2`, or on whether it is zero, the limit is computed for each
possibility (`a < 2`, `a == 2`, `a > 2`), a zero by solving for a parameter and
substituting. Cases with the same limit are merged. Returns a [`LimitCases`](@ref).

`signs` is as for `gruntz_limit`, and restricts the cases. Parameters are not taken
to be nonzero, so `a == 0` is a case where it matters.

```jldoctest
julia> using GruntzLimit

julia> gruntz_cases(:(x^(a - 2)), :x)
LimitCases with 3 cases:
  a < 2  =>  0
  a == 2  =>  1
  a > 2  =>  Inf

julia> gruntz_cases(:(a^x), :x)
LimitCases with 4 cases:
  a <= 0  =>  undefined
  0 < a < 1  =>  0
  a == 1  =>  1
  a > 1  =>  Inf
```
"""
function gruntz_cases(f, x, x0 = Inf; dir::Symbol = :+, build = nothing, lift = nothing,
                      signs = ())
    xa = leafatom(x)
    ctx, sub = signs_context(signs, xa)
    bd = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift)
    tree = solve_cases(() -> limit_value(f, xa, x0, dir), ctx, sub, xa, 0, Ref(0))
    merged = with_context(() -> merge_cases(flatten_cases(tree, Tuple{Sum,Symbol}[], [])), ctx, sub, false, xa)
    cases = with_context(ctx, sub, false, xa) do
        [CaseCondition[show_condition(bd, c, r) for (c, r) in conds] => user_value(bd, v)
         for (conds, v) in merged]
    end
    # in order of the conditions: a < 2, a == 2, a > 2
    order = sortperm(cases; by = p -> [(string(c.lhs), string(c.rhs), REL_RANK[c.rel]) for c in p.first])
    LimitCases(cases[order], [Tuple{Sum,Symbol}[l for l in merged[i].first] for i in order], ctx, sub,
               Any[merged[i].second for i in order], bd)
end
