# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
function lim_equal(a, b)
    (a isa Infinity && b isa Infinity) && return signof(a) == signof(b)
    (a isa Sum && b isa Sum) && return skey(a) == skey(b)
    false
end

function with_context(g, ctx::Vector{Cond}, sub::Dict{String,Sum}, cases::Bool, x::Atom)
    old = (CTX[], SUBST[], CASES[], XATOM[], SIGN_CACHE[])
    CTX[], SUBST[], CASES[], XATOM[] = ctx, sub, cases, x
    SIGN_CACHE[] = Dict{Tuple{String,Bool},Vector{Int}}()
    try
        g()
    finally
        CTX[], SUBST[], CASES[], XATOM[], SIGN_CACHE[] = old
    end
end

substS(s::Sum, sub::Dict{String,Sum}) =
    isempty(sub) ? s : subs_atoms(s, a -> a.kind === :leaf ? get(sub, a.key, nothing) : nothing)

# Solves c = 0 for a parameter p, when c = k p + r or k log(p) + r with r free of p,
# or c = k p^n with n > 0. Returns p's key => its value, or nothing.
function solve_zero(c::Sum)
    for (m, k) in sort!(collect(c.t); by = p -> p.first.key)
        length(m.fs) == 1 || continue
        a, e = m.fs[1]
        p = a.kind === :leaf ? a : a.kind === :fun && a.head === :log ? single_atom(a.args[1]::Sum) : nothing
        (p === nothing || !isparam(p)) && continue
        r = subS(c, monoS(m, k))
        hasleaf(r, p.key) && continue
        a == p && isempty(r.t) && e > 0 && return p.key => zeroS()
        isone(e) || continue
        v = scaleS(r, -inv(k))
        return p.key => (a == p ? v : mkexp(v))
    end
    nothing
end

# adds the substitution p => v, applying it to the values already there
function add_subst!(sub::Dict{String,Sum}, pv::Pair{String,Sum})
    one = Dict(pv)
    for (k, v) in sub
        sub[k] = substS(v, one)
    end
    sub[pv.first] = pv.second
    sub
end

# The context with the substitutions applied; nothing if it became false
function subst_ctx(ctx::Vector{Cond}, sub::Dict{String,Sum})
    out = Cond[]
    for cd in ctx
        c = substS(cd.c, sub)
        r = ratconst(c)
        if r === nothing
            push!(out, normcond(c, cd.rel))
        else
            ok = cd.rel === :> ? r > 0 : cd.rel === :< ? r < 0 : cd.rel === :>= ? r >= 0 :
                 cd.rel === :<= ? r <= 0 : cd.rel === :(==) ? iszero(r) : !iszero(r)
            ok || return nothing
        end
    end
    out
end

# the values of `signs`, as relations to 0
const SIGN_RELS = Dict(:positive => :>, :negative => :<, :nonnegative => :>=,
                       :nonpositive => :<=, :zero => :(==), :nonzero => :!=)

# The context and substitutions given by `signs`: pairs `c => s`, `c` a parameter or
# an expression in parameters and `s` a key of `SIGN_RELS`. A zero is solved for a
# parameter and substituted.
function signs_context(signs, x::Atom)
    ctx, sub = Cond[], Dict{String,Sum}()
    zs = Sum[]
    for (p, sg) in signs
        haskey(SIGN_RELS, sg) || throw(ArgumentError("the sign of `$p` must be one of " *
            join(repr.(sort!(collect(keys(SIGN_RELS)))), ", ") * "; got $(repr(sg))"))
        c = from_term(p)
        ratconst(c) === nothing || throw(ArgumentError("`$p` has no parameter"))
        sg === :zero ? push!(zs, c) : push!(ctx, normcond(c, SIGN_RELS[sg]))
    end
    with_context(Cond[], sub, false, x) do
        for c in zs
            sol = solve_zero(substS(c, sub))
            sol === nothing && throw(ArgumentError("cannot solve `$(skey(c)) = 0` for a parameter"))
            add_subst!(sub, sol)
        end
        ctx = subst_ctx(ctx, sub)
    end
    ctx === nothing && throw(ArgumentError("the signs given are contradictory"))
    ctx, sub
end

# +1 / -1 for +/-infinity (Julia floats or a symbolic package's infinity), else 0
function infdir(x0)
    x0 isa AbstractFloat && return isinf(x0) ? (x0 > 0 ? 1 : -1) : 0
    x0 isa Number || return 0
    s = string(x0)
    s in ("Inf", "+Inf", "inf", "oo", "+oo", "Infinity") ? 1 :
    s in ("-Inf", "-inf", "-oo", "-Infinity") ? -1 : 0
end

# At x -> +oo every expression handled here has an eventual constant sign, so
# abs(u) = sign(u) * u. Inner abs are resolved first. An abs of a constant whose
# sign cannot be decided (free parameter) stays as an `abs` atom.
function resolve_abs(e::Sum, x::Atom)
    function res(a::Atom)
        (a.kind === :fun && a.head === :abs) || return nothing
        u = subs_atoms(a.args[1]::Sum, res)
        hasleaf(u, x.key) && return scaleS(u, Q(sgn(u, x)))
        sg = try
            csign(u)
        catch err
            err isa NeedSign ? nothing : rethrow()
        end
        sg === nothing ? mkabs(u) : scaleS(u, Q(sg))
    end
    subs_atoms(e, res)
end

limit_pos(e::Sum, x::Atom) = limitinf(resolve_abs(e, x), x)

function _limit(e::Sum, xa::Atom, x0, dir::Symbol)
    xS = atomS(xa)
    inf = infdir(x0)
    if inf != 0
        return inf > 0 ? limit_pos(e, xa) :
               limit_pos(subs_atoms(e, a -> a == xa ? negS(xS) : nothing), xa)
    end
    p = from_term(x0)
    hasleaf(p, xa.key) && throw(GruntzError("the limit point must not contain the variable"))
    inv_x = powS(xS, Q(-1))
    side(sg) = limit_pos(subs_atoms(e, a -> a == xa ? addS(p, scaleS(inv_x, Q(sg))) : nothing), xa)
    if dir === :+
        side(1)
    elseif dir === :-
        side(-1)
    elseif dir === :both
        l, r = side(1), side(-1)
        lim_equal(l, r) || throw(GruntzError("one-sided limits differ", :nolimit))
        l
    else
        throw(GruntzError("dir must be :+, :- or :both"))
    end
end

# Callable term types (SimpleExpressions): a constant such as π becomes a term,
# π * one(x), the same as a user writes it.
function callable_lift(x)
    v -> v isa AbstractIrrational ? (try v * one(x) catch; v end) : v
end

# Symbolic number types that are not `Real` (e.g. SymEngine's `Basic`) are built
# from plain numbers by their constructor, so results like exp(1) stay exact.
function auto_lift(f, x)
    for t in (f, x)
        if t isa Number && !(t isa Real)
            T = typeof(t)
            return v -> try
                T(v)
            catch
                v
            end
        end
    end
    other_terms(x) ? term_lift(x) : x isa Function ? callable_lift(x) : identity
end

"""
    gruntz_limit(f, x, x0 = Inf; dir = :+, build = nothing, lift = nothing, signs = ())

Compute ``\\lim_{x \\to x_0} f(x)`` with Gruntz's algorithm.

* `f`: a symbolic expression implementing TermInterface's `iscall`, `operation` and
  `arguments` (e.g. a SymEngine `Basic` or a Julia `Expr`).
* `x`: the variable, the same object that appears in `f` (a `Basic` symbol, or a
  `Symbol` for an `Expr`).
* `x0`: `Inf`, `-Inf`, or a finite point: a number or an expression not containing `x`.
* `dir`: `:+` (from the right, the default), `:-` (from the left) or `:both` (both
  one-sided limits must agree). Only used for finite `x0`.
* `build`: `build(op, args...)` constructs a compound result term. When `x` is a
  `Symbol` (`Expr` input) the default is `Expr(:call, nameof(op), args...)`, giving an
  unevaluated `Expr`; otherwise it calls `op(args...)`, which is right for types like
  SymEngine's `Basic`.
* `lift`: converts plain Julia numbers (and `π`) in the result to the symbolic number
  type. The default uses the constructor of `typeof(f)` when that is a non-`Real`
  `Number` (as with `Basic`); otherwise numbers are left as they are.
* `signs` (**experimental**, may change): signs of parameters, or of expressions in them,
  as pairs `c => s` with `s` one of `:positive`, `:negative`, `:nonnegative`,
  `:nonpositive`, `:zero` or `:nonzero` (e.g. `Dict(a => :positive)` or
  `Dict(a - 2 => :negative)`). `c` is written like `f`: a `Symbol` or `Expr` for an `Expr`,
  a term of the same package otherwise. Consequences are used (`a > 2` from `a - 2 > 0`).
  A zero is solved for a parameter, which is substituted. Without them, a parameter is a real number
  of unknown sign. When the limit depends on a sign that is not decided, a `GruntzError`
  names the constant (see [`gruntz_cases`](@ref)). A constant that may or may not be zero is
  taken to be nonzero, so answers are generic (`a/b` for `b != 0`).

Returns `Inf`, `-Inf`, an `Int`/`Rational` for rational limits, or otherwise a term
assembled with `build`. Throws [`GruntzError`](@ref) when the limit does not exist or
cannot be computed.

# Examples

```jldoctest
julia> using GruntzLimit

julia> gruntz_limit(:(sin(x)/x), :x, 0)
1

julia> gruntz_limit(:(1/x), :x, 0; dir = :-)
-Inf

julia> gruntz_limit(:((1 + a/x)^x), :x)
:(exp(a))

julia> gruntz_limit(:(atan(x)), :x)
:(1//2 * π)
```
"""
function gruntz_limit(f, x, x0 = Inf; dir::Symbol = :+, build = nothing, lift = nothing,
                      signs = ())
    xa = leafatom(x)
    ctx, sub = signs_context(signs, xa)
    bd = Builder(build === nothing ? auto_build(f, x) : build,
                 lift === nothing ? auto_lift(f, x) : lift)
    L = with_context(ctx, sub, false, xa) do
        try
            limit_value(f, xa, x0, dir)
        catch err
            err isa NeedSign || rethrow()
            c = show_condition(bd, split_target(err.c), :>)
            throw(GruntzError("the limit depends on the sign of `$(difference(c))`, which " *
                              "cannot be decided: give it with `signs`, or use `gruntz_cases`"))
        end
    end
    user_value(bd, L)
end

# lhs - rhs of a condition, as a string
function difference(c)
    c.rhs isa Number && iszero(c.rhs) && return string(c.lhs)
    c.rhs isa Real && c.rhs < 0 && return string(c.lhs, " + ", -c.rhs)
    string(c.lhs, " - ", c.rhs)
end

# the limit, an infinite one with its sign decided
function limit_value(f, xa::Atom, x0, dir::Symbol)
    L = _limit(from_term(f), xa, x0, dir)
    L isa Infinity && signof(L)
    L
end

function user_value(bd::Builder, L)
    L isa Infinity && return signof(L) > 0 ? Inf : -Inf
    if L isa GruntzError
        return L.kind === :fail ? L : L.kind
    end
    r = ratconst(L)
    r !== nothing && return num(r)
    to_term(bd, L)
end
