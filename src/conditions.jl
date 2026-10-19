# ---------------------------------------------------------------------------
# Conditions on parameters
# ---------------------------------------------------------------------------
# A parameter is a leaf, other than x, that is not a number. The *context* of a
# limit is a list of conditions on constants with parameters (`a - 2 > 0`), from
# `signs` and, in `gruntz_cases`, from splitting into cases. A sign the context does
# not decide raises `NeedSign`: `gruntz_cases` splits on it, `gruntz_limit` reports
# it. A parameter given a value (the case `a - 2 = 0`) is substituted when terms are
# converted (`SUBST`).

# c > 0, c < 0, c >= 0, c <= 0, c == 0 or c != 0, c normalised by `normcond`
struct Cond
    c::Sum
    rel::Symbol
end

const CTX = Ref(Cond[])
const SUBST = Ref(Dict{String,Sum}())     # parameter key => value
const CASES = Ref(false)                  # splitting into cases (`gruntz_cases`)
const XATOM = Ref(WLEAF)                  # the limit variable
const SIGN_CACHE = Ref(Dict{Tuple{String,Bool},Vector{Int}}())   # for CTX: possible signs

# The sign of the constant `c` is needed; `possible` are the signs the context
# allows. For a zero test (`zerotest`) only whether c is zero matters.
struct NeedSign <: Exception
    c::Sum
    possible::Vector{Int}
    zerotest::Bool
end

flip(rel::Symbol) = rel === :> ? :< : rel === :< ? :> : rel === :>= ? :<= : rel === :<= ? :>= : rel

# c scaled so that its first non-constant monomial has coefficient 1
function normcond(c::Sum, rel::Symbol)
    ms = sort!([m for m in keys(c.t) if !isempty(m.fs)]; by = m -> m.key)
    isempty(ms) && return Cond(c, rel)
    k = c.t[ms[1]]
    Cond(scaleS(c, inv(k)), k < 0 ? flip(rel) : rel)
end

isparam(a::Atom, x::Atom = XATOM[]) =
    a.kind === :leaf && a != x && !iswleaf(a) && numval_or_nothing(a) === nothing

# c as a linear form in its parameter monomials, their numeric factors evaluated:
# (monomial key => coefficient, constant). `vars` collects the monomials.
function linform(c::Sum, vars::Dict{String,Mono})
    d = Dict{String,BigFloat}()
    k0 = BigFloat(0)
    for (m, q) in c.t
        v = bigq(q)
        fs = Pair{Atom,Q}[]
        for (a, e) in m.fs
            nv = numval_or_nothing(a)
            nv === nothing ? push!(fs, a => e) : (v *= nv^bigq(e))
        end
        if isempty(fs)
            k0 += v
        else
            pm = Mono(fs)
            vars[pm.key] = pm
            d[pm.key] = get(d, pm.key, BigFloat(0)) + v
        end
    end
    d, k0
end


function ineqs(cd::Cond, vars::Dict{String,Mono})
    a, k = linform(cd.c, vars)
    cd.rel === :> ? [Ineq(a, k, true)] :
    cd.rel === :< ? [Ineq(negate(a), -k, true)] :
    cd.rel === :>= ? [Ineq(a, k, false)] :
    cd.rel === :<= ? [Ineq(negate(a), -k, false)] :
    cd.rel === :(==) ? [Ineq(a, k, false), Ineq(negate(a), -k, false)] : Ineq[]
end

# The sign of an atom with parameters, from the context (linear reasoning only):
# ±1 or nothing. log(s) has the sign of s - 1; abs is taken to be positive (a zero
# argument is split off as a case of its own).
function atom_sign(a::Atom)
    a.kind === :fun && a.head in (:exp, :abs) && return 1
    s = a.kind === :leaf ? atomS(a) :
        a.kind === :base ? a.args[1]::Sum :
        a.kind === :fun && a.head === :log ? subS(a.args[1]::Sum, oneS()) :
        a.kind === :fun && a.head === :atan ? a.args[1]::Sum : nothing
    s === nothing && return nothing
    ps = possible_signs(s; facts = false)
    length(ps) == 1 && ps[1] != 0 ? ps[1] : nothing
end

function mono_sign(m::Mono)
    sg = 1
    for (a, e) in m.fs
        sa = atom_sign(a)
        sa === nothing && return nothing
        if sa < 0
            isone(denominator(e)) || return nothing
            isodd(numerator(e)) && (sg = -sg)
        end
    end
    sg
end

# the signs of the monomials that are not a single parameter, from their factors
function fact_ineqs(vars::Dict{String,Mono})
    out = Ineq[]
    for (key, m) in vars
        (length(m.fs) == 1 && isone(m.fs[1].second) && m.fs[1].first.kind === :leaf) && continue
        sg = mono_sign(m)
        sg === nothing || push!(out, Ineq(Dict{String,BigFloat}(key => BigFloat(sg)), BigFloat(0), true))
    end
    out
end

# whether the conditions `c rel 0` (rel one of < <= == != >= >) and the context
# can hold together
function satisfiable(clist::Vector{Tuple{Sum,Symbol}})
    i = findfirst(l -> l[2] === :!=, clist)
    if i !== nothing
        c, rest = clist[i][1], deleteat!(copy(clist), i)
        return satisfiable(push!(copy(rest), (c, :<))) || satisfiable(push!(rest, (c, :>)))
    end
    vars = Dict{String,Mono}()
    base = Ineq[]
    for cd in CTX[]
        append!(base, ineqs(cd, vars))
    end
    for (c, rel) in clist
        a, k = linform(c, vars)
        rel in (:>, :>=, :(==)) && push!(base, Ineq(a, k, rel === :>))
        rel in (:<, :<=, :(==)) && push!(base, Ineq(negate(a), -k, rel === :<))
    end
    feasible(append!(base, fact_ineqs(vars)))
end
negations(rel::Symbol) = rel === :< ? [:>=] : rel === :<= ? [:>] : rel === :> ? [:<=] :
                         rel === :>= ? [:<] : rel === :(==) ? [:<, :>] : [:(==)]

# s with the powers of parameters (or of their functions) that divide every term, or
# are in a denominator, taken out when their signs are known: a/b - 1 becomes a - b.
# Returns (s', σ) with sign(s) = σ sign(s').
function clear_factors(s::Sum)
    length(s.t) < 2 && return s, 1
    lows = Dict{String,Tuple{Atom,Q}}()
    for m in keys(s.t), (a, e) in m.fs
        numval_or_nothing(a) === nothing || continue
        lows[a.key] = (a, min(e, get(lows, a.key, (a, e))[2]))
    end
    for (k, (a, e)) in lows
        all(m -> any(p -> p.first.key == k, m.fs), keys(s.t)) || (lows[k] = (a, min(e, zero(Q))))
    end
    σ = 1
    fs = Pair{Atom,Q}[]
    for (a, e) in values(lows)
        iszero(e) && continue
        sa = atom_sign(a)
        sa === nothing && continue
        if sa < 0
            isone(denominator(e)) || continue
            isodd(numerator(e)) && (σ = -σ)
        end
        push!(fs, a => -e)
    end
    isempty(fs) && return s, 1
    mulS(s, monoS(mono(Dict{Atom,Q}(fs)), Q(1))), σ
end

known_nonzero(s::Sum) =
    (k = skey(normcond(s, :!=).c); any(cd -> cd.rel === :!= && skey(cd.c) == k, CTX[]))

# The signs of the constant `s` that the context allows. With `facts`, the signs of
# products and functions of parameters (a*b, 1/a, log(a)) are derived from their
# factors' signs.
possible_signs(s::Sum; facts::Bool = true) =
    copy(get!(() -> _possible_signs(s, facts), SIGN_CACHE[], (skey(s), facts)))
function _possible_signs(s::Sum, facts::Bool)
    if facts
        s2, σ = clear_factors(s)
        σ == 1 || return sort!([-p for p in possible_signs(s2)])
        s = s2
    end
    vars = Dict{String,Mono}()
    base = Ineq[]
    for cd in CTX[]
        append!(base, ineqs(cd, vars))
    end
    a, k = linform(s, vars)
    if all(t -> abs(t) <= FM_TOL, values(a))
        return abs(k) <= FM_TOL ? [0] : [k > 0 ? 1 : -1]
    end
    facts && append!(base, fact_ineqs(vars))
    out = Int[]
    feasible(push!(copy(base), Ineq(negate(a), -k, true))) && push!(out, -1)
    !known_nonzero(s) && feasible(append!(copy(base), [Ineq(a, k, false), Ineq(negate(a), -k, false)])) &&
        push!(out, 0)
    feasible(push!(copy(base), Ineq(a, k, true))) && push!(out, 1)
    out
end

function csign(s::Sum)::Int
    isempty(s.t) && return 0
    r = ratconst(s)
    r !== nothing && return Int(sign(r))
    v = try
        numval(s)
    catch err
        err isa FreeSymbol || throw(GruntzError("cannot evaluate constant $(skey(s))"))
        nothing
    end
    v === nothing || return abs(v) < big"1e-60" ? 0 : (v > 0 ? 1 : -1)
    ps = possible_signs(s)
    isempty(ps) && throw(GruntzError("the conditions on the parameters are contradictory"))
    CASES[] || length(ps) == 1 || filter!(!=(0), ps)   # generic values: nonzero
    length(ps) == 1 ? ps[1] : throw(NeedSign(s, ps, false))
end

# Whether the constant `s` is zero: true, false, or the `NeedSign` to throw when the
# context does not decide it. A numerically zero constant is a zero the simplifier
# did not recognise. A constant with parameters is taken to be nonzero, except when
# splitting into cases.
function zerostate(s::Sum)
    isempty(s.t) && return true
    v = try
        numval(s)
    catch err
        err isa FreeSymbol || return false
        nothing
    end
    v === nothing || return abs(v) < big"1e-60"
    CASES[] || return false
    ps = possible_signs(s)
    ps == [0] && return true
    0 in ps ? NeedSign(s, ps, true) : false
end

# log needs a positive argument: when splitting into cases, a constant (factor)
# with parameters is checked
function require_positive(s::Sum)
    hasvar(a::Atom) = hasleaf(a, XATOM[].key) || hasw(a)
    k = if length(s.t) == 1
        m, c = first(s.t)
        monoS(Mono(filter(p -> !hasvar(p.first), m.fs)), c)
    elseif any(m -> any(p -> hasvar(p.first), m.fs), keys(s.t))
        return
    else
        s
    end
    ratconst(k) === nothing || return
    any(m -> any(p -> numval_or_nothing(p.first) === nothing, m.fs), keys(k.t)) || return
    ps = possible_signs(k)
    ps == [1] && return
    1 in ps || throw(GruntzError("log of a number that is not positive", :undefined))
    throw(NeedSign(k, ps, false))
end
