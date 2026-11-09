# ---------------------------------------------------------------------------
# Conditions on parameters
# ---------------------------------------------------------------------------
# A parameter is a leaf, other than x, that is not a number. The *context* of a
# limit is a list of conditions on constants with parameters (`a - 2 > 0`), from
# `signs` and, in `gruntz_cases`, from splitting into cases. A sign the context does
# not decide raises `NeedSign`: `gruntz_cases` splits on it, `gruntz_limit` reports
# it. A parameter given a value (the case `a - 2 = 0`) is substituted when terms are
# converted (`subst` of the context).

# c > 0, c < 0, c >= 0, c <= 0, c == 0 or c != 0, c normalised by `normcond`
struct Cond
    c::Sum
    rel::Symbol
end

# The context of the limit being computed. It is set by `with_context` (below) for
# the extent of a call, in a `ScopedValue`, so concurrent limits each see their own.
# Read by the sign and zero tests here, by `series.jl`, `constructors.jl` (cases),
# `from_term.jl` (subst) and `cases.jl` (x).
struct Context
    conds::Vector{Cond}
    subst::Dict{String,Sum}       # parameter key => value
    cases::Bool                   # splitting into cases (`gruntz_cases`)
    x::Atom                       # the limit variable
    sign_cache::Union{Nothing,Dict{Tuple{String,Bool},Vector{Int}}}   # possible signs
    limit_cache::Union{Nothing,Dict{Tuple{String,String},Any}}        # `limitinf` results
end
# outside `with_context` (converting `signs`): no conditions, and no cache to share
const CONTEXT = ScopedValue(Context(Cond[], Dict{String,Sum}(), false, WLEAF, nothing, nothing))

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

isparam(a::Atom, x::Atom = CONTEXT[].x) =
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
# ±1 or nothing. log(s) has the sign of s - 1, sign(s) that of s; abs is taken to be positive (a zero
# argument is split off as a case of its own). erf(s) has the sign of s, erfs is positive,
# as are lgrem, fsi and gsi (their arguments tend to +oo) and gamma of a positive number.
# sinint, erfi and dawson have the sign of their argument, as has li2 (real for u <= 1).
function atom_sign(a::Atom)
    a.kind === :fun && a.head in (:exp, :abs, :erfs, :lgrem, :fsi, :gsi) && return 1
    if a.kind === :fun && a.head === :gamma
        return possible_signs(a.args[1]::Sum; facts = false) == [1] ? 1 : nothing
    end
    s = a.kind === :leaf ? atomS(a) :
        a.kind === :base ? a.args[1]::Sum :
        a.kind === :fun && a.head === :log ? subS(a.args[1]::Sum, oneS()) :
        a.kind === :fun && a.head in (:atan, :erf, :sign, :sinint, :erfi, :dawson, :li2) ? a.args[1]::Sum : nothing
    s === nothing && return nothing
    # a perfect square c p², c > 0, positive where p ≠ 0: (1 + 2M + M²)⁻¹
    if a.kind === :base && !hasvar(a)
        r = sqrt_poly(s)
        r !== nothing && (known_nonzero(s) || !(0 in possible_signs(r[2]; facts = false))) && return 1
    end
    # a base's own factors are used ((1 + M)/(1 + 2M + M²) for M > -1); its argument is
    # smaller, so this ends
    ps = possible_signs(s; facts = a.kind === :base && !hasvar(a))
    length(ps) == 1 && ps[1] != 0 ? ps[1] : nothing
end

# a fractional power is positive: its base is checked when it is made (see
# `require_positive`)
function mono_sign(m::Mono)
    sg = 1
    for (a, e) in m.fs
        isone(denominator(e)) || continue
        sa = atom_sign(a)
        sa === nothing && return nothing
        sa < 0 && isodd(numerator(e)) && (sg = -sg)
    end
    sg
end

# the signs of the monomials that are not a single parameter, from their factors
function fact_ineqs(vars::Dict{String,Mono})
    out = Ineq[]
    for (key, m) in vars
        (length(m.fs) == 1 && isone(m.fs[1].second) && m.fs[1].first.kind === :leaf) && continue
        sg = mono_sign(m)
        if sg !== nothing
            push!(out, Ineq(Dict{String,BigFloat}(key => BigFloat(sg)), BigFloat(0), true))
        else
            # factors of undecided sign with even exponents: σ m ≥ 0 (a², a² b for b > 0)
            sg = mono_sign(Mono(filter(p -> !(isone(denominator(p.second)) && iseven(numerator(p.second))), m.fs)))
            sg === nothing || push!(out, Ineq(Dict{String,BigFloat}(key => BigFloat(sg)), BigFloat(0), false))
        end
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
    for cd in CONTEXT[].conds
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
        sa = isone(denominator(e)) ? atom_sign(a) : 1   # as in `mono_sign`
        sa === nothing && continue
        sa < 0 && isodd(numerator(e)) && (σ = -σ)
        push!(fs, a => -e)
    end
    isempty(fs) && return s, 1
    mulS(s, monoS(mono(Dict{Atom,Q}(fs)), Q(1))), σ
end

known_nonzero(s::Sum) =
    (k = skey(normcond(s, :!=).c); any(cd -> cd.rel === :!= && skey(cd.c) == k, CONTEXT[].conds))

# The signs of the constant `s` that the context allows. With `facts`, the signs of
# products and functions of parameters (a*b, 1/a, log(a)) are derived from their
# factors' signs.
function possible_signs(s::Sum; facts::Bool = true)
    cache = CONTEXT[].sign_cache
    cache === nothing && return _possible_signs(s, facts)
    k = (skey(s), facts)
    haskey(cache, k) && return copy(cache[k])
    # a re-entrant call for s, from the signs of its factors or atoms (see `atom_sign`),
    # finds every sign possible instead of recursing without end
    cache[k] = [-1, 0, 1]
    ps = try
        _possible_signs(s, facts)
    catch
        delete!(cache, k)
        rethrow()
    end
    cache[k] = ps
    copy(ps)
end
function _possible_signs(s::Sum, facts::Bool)
    if facts
        s2, σ = clear_factors(s)
        σ == 1 || return sort!([-p for p in possible_signs(s2)])
        s = s2
    end
    vars = Dict{String,Mono}()
    base = Ineq[]
    for cd in CONTEXT[].conds
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
    CONTEXT[].cases || length(ps) == 1 || filter!(!=(0), ps)   # generic values: nonzero
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
    if !CONTEXT[].cases
        # p - |p| vanishes for every p ≥ 0, not at isolated values: not generic, so the
        # sign of p is needed (√((M+1)²) = |M+1|, SymPy #23525)
        q = abs_cancel(s)
        q === nothing && return false
        ps = possible_signs(q)
        return length(setdiff(ps, [0])) > 1 ? NeedSign(q, ps, false) : false
    end
    ps = possible_signs(s)
    ps == [0] && return true
    0 in ps ? NeedSign(s, ps, true) : false
end

# The argument q of an atom |q| of the constant s for which s vanishes identically
# when |q| is taken as q or as -q; or nothing
function abs_cancel(s::Sum)
    seen = Set{String}()
    for m in keys(s.t), (a, _) in m.fs
        (a.kind === :fun && a.head === :abs && !(a.key in seen)) || continue
        push!(seen, a.key)
        q = a.args[1]::Sum
        for r in (q, negS(q))
            isempty(subs_atoms(s, b -> b.key == a.key ? r : nothing).t) && return q
        end
    end
    nothing
end

hasvar(a::Atom) = hasleaf(a, CONTEXT[].x.key) || hasw(a)

# c*m, for log and fractional powers, which are taken factor by factor, as a product
# of positive factors: (|c|, kept, negs, grp). `kept` are the factors taken as they
# are: of x, numbers, fractional powers, and parameters known to be positive. `negs`
# are those known to be negative, with an integer exponent: each is taken as -a. Atoms
# of x such as log(x), once x is the variable that tends to +oo (see DEFER_DOMAIN), are
# put in one or the other by their eventual sign (see `varsign`). The
# others, of undecided sign, are taken as they are outside case splitting when the
# product is positive (parameters are generic); otherwise they are grouped, with the
# sign, as the one positive constant `grp` (log(-a*b), a < 0 < b undecided...).
# `nothing` when the factors' signs make c*m negative.
function positive_factors(m::Mono, c::Q)
    kept, negs, und = Pair{Atom,Q}[], Pair{Atom,Q}[], Pair{Atom,Q}[]
    σ = c < 0 ? -1 : 1
    for (a, e) in m.fs
        if hasvar(a) && !(isone(denominator(e)) && signable(a) && !_defer_domain(m))
            push!(kept, a => e)
            continue
        end
        if !hasvar(a) && (numval_or_nothing(a) !== nothing || !isone(denominator(e)))
            push!(kept, a => e)
            continue
        end
        sa = hasvar(a) ? varsign(a) : atom_sign(a)
        sa == 0 && hasvar(a) && (sa = 1)
        if sa == 1
            push!(kept, a => e)
        elseif sa == -1
            push!(negs, a => e)
            isodd(numerator(e)) && (σ = -σ)
        else
            push!(und, a => e)
        end
    end
    grp = nothing
    if !isempty(und)
        if σ > 0 && !CONTEXT[].cases
            append!(kept, und)
        else
            grp = monoS(mono(Dict{Atom,Q}(und)), Q(σ))
            σ = 1
        end
    end
    σ < 0 && return nothing
    abs(c), mono(Dict{Atom,Q}(kept)), negs, grp
end
# whether c*m needs `positive_factors`: a negative coefficient, or a parameter
needs_signs(m::Mono, c::Q) =
    c < 0 || any(p -> !hasvar(p.first) && numval_or_nothing(p.first) === nothing, m.fs)
negatom(a::Atom) = scaleS(atomS(a), Q(-1))

# log needs a positive argument, a fractional power a nonnegative one (positive for a
# negative exponent: `strict`): a constant (factor) with parameters is checked. One
# the context rules out is an error; one it does not decide is split on when
# splitting into cases, and otherwise taken to be valid (parameters are generic).
function require_positive(s::Sum; strict::Bool = true, what::String = "log")
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
    (ps == [1] || ps == [0]) && return
    any(p -> p > 0 || (p == 0 && !strict), ps) ||
        throw(GruntzError("$what of a number that is not " * (strict ? "positive" : "nonnegative"), :undefined))
    CONTEXT[].cases && throw(NeedSign(k, ps, false))
end

# ---------------------------------------------------------------------------
# Setting the context; substituting values for parameters
# ---------------------------------------------------------------------------
with_context(g, ctx::Vector{Cond}, sub::Dict{String,Sum}, cases::Bool, x::Atom) =
    with(g, CONTEXT => Context(ctx, sub, cases, x, Dict{Tuple{String,Bool},Vector{Int}}(),
                               Dict{Tuple{String,String},Any}()))

substS(s::Sum, sub::Dict{String,Sum}) =
    isempty(sub) ? s : subs_atoms(s, a -> a.kind === :leaf ? get(sub, a.key, nothing) : nothing)

# The parameter p of an atom p, log(p) or log(-p), and which of the three it is
# (:id, :log, :neglog); or nothing
function param_of(a::Atom)
    a.kind === :leaf && return isparam(a) ? (a, :id) : nothing
    (a.kind === :fun && a.head === :log) || return nothing
    s = a.args[1]::Sum
    for (u, how) in ((s, :log), (negS(s), :neglog))
        p = single_atom(u)
        p !== nothing && isparam(p) && return (p, how)
    end
    nothing
end
# p from the value v of its atom (p, log(p) or log(-p))
param_value(how::Symbol, v::Sum) = how === :id ? v : how === :log ? mkexp(v) : negS(mkexp(v))

# Solves c = 0 for a parameter p, when c = k p + r, k log(p) + r or k log(-p) + r with
# r free of p, or c = k p^n with n > 0. Also, when c is linear in p with coefficients in
# the other parameters, c = A p + B, for A or B a nonzero number (x = -1/ρ for
# 1 + ρ x = 0); and k exp(u) + k0 = 0 as u = log(-k0/k). Returns p's key => its value,
# or nothing.
solve_zero(c::Sum) = solve_zero_cond(c)[1]

# c times the parameters in its denominators: 1/M1 + 1/M2 as M2 + M1 (the parameters
# are nonzero where c is defined)
function clear_denoms(c::Sum)
    length(c.t) < 2 && return c
    low = Dict{String,Tuple{Atom,Q}}()
    for m in keys(c.t), (a, e) in m.fs
        (isparam(a) && e < 0) || continue
        low[a.key] = (a, min(e, get(low, a.key, (a, e))[2]))
    end
    isempty(low) && return c
    mulS(c, monoS(mono(Dict{Atom,Q}(a => -e for (a, e) in values(low))), Q(1)))
end

# a parameter p with p^n (n > 0) dividing every term of c: (p, n), or nothing
function common_param(c::Sum)
    ps = common_params(c)
    isempty(ps) && return nothing
    a = ps[1]
    a, minimum(sum((e for (b, e) in m.fs if b == a); init = Q(0)) for m in keys(c.t))
end
# the parameters dividing every term of c (with two terms or more)
function common_params(c::Sum)
    length(c.t) < 2 && return Atom[]
    ms = collect(keys(c.t))
    [a for (a, _) in ms[1].fs if isparam(a) &&
         all(m -> sum((e for (b, e) in m.fs if b == a); init = Q(0)) > 0, ms)]
end

# The same, with the condition the solution needs (A ≠ 0 for p = -B/A, as a Sum that
# must be nonzero), or nothing
function solve_zero_cond(c::Sum)
    if !any(m -> any(p -> hasvar(p.first), m.fs), keys(c.t))
        # parameters in denominators (nonzero there) and factors of known sign cleared:
        # 2C/M1 + 2C/M2 = 0 as M1 + M2 = 0
        c2 = clear_factors(clear_denoms(c))[1]
        skey(c2) == skey(c) || return solve_zero_cond(c2)
        # p^n r = 0 with r nonzero in the context as p = 0: (M1 + M2) a² = 0, M1 + M2 > 0
        p = common_param(c)
        if p !== nothing
            r = mulS(c, powS(atomS(p[1]), -p[2]))
            0 in possible_signs(r) || return solve_zero_cond(atomS(p[1]))
        end
        # c p² = 0 as p = 0: (M1 + M2)² = 0
        r = sqrt_poly(c)
        r === nothing || return solve_zero_cond(r[2])
    end
    sol = solve_zero_simple(c)
    sol === nothing || return sol, nothing
    r = solve_linear(c)
    r === nothing || return r
    if length(c.t) == 2                          # k exp(u)^e + k0
        k0 = ratconst(subS(c, Sum(Dict(m => q for (m, q) in c.t if !isempty(m.fs)))))
        ms = [(m, q) for (m, q) in c.t if !isempty(m.fs)]
        if k0 !== nothing && !iszero(k0) && length(ms) == 1
            m, k = ms[1]
            if length(m.fs) == 1 && m.fs[1].first.kind === :fun && m.fs[1].first.head === :exp &&
               -k0 / k > 0
                a, e = m.fs[1]
                return solve_zero_cond(subS(scaleS(a.args[1]::Sum, e), lograt(-k0 / k)))
            end
        end
    end
    nothing, nothing
end

# c = A p + B, A and B free of the parameter p, A or B a nonzero number
function solve_linear(c::Sum)
    ps = Dict{String,Atom}()
    for m in keys(c.t), (a, _) in m.fs
        isparam(a) && (ps[a.key] = a)
    end
    for k in sort!(collect(keys(ps)))
        p = ps[k]
        A, B, ok = zeroS(), zeroS(), true
        for (m, q) in c.t
            e = zero(Q)
            for (a, ea) in m.fs
                if a == p
                    e = ea
                elseif hasleaf(a, k)
                    ok = false
                end
            end
            (ok && (iszero(e) || isone(e))) || (ok = false; break)
            rest = monoS(Mono(filter(f -> f.first != p, m.fs)), q)
            iszero(e) ? (B = addS(B, rest)) : (A = addS(A, rest))
        end
        ok && !iszero(A) || continue
        ra, rb = ratconst(A), ratconst(B)
        (ra !== nothing || (rb !== nothing && !iszero(rb))) || continue
        return p.key => negS(mulS(B, powS(A, Q(-1)))), (ra === nothing ? A : nothing)
    end
    nothing
end

function solve_zero_simple(c::Sum)
    for (m, k) in sort!(collect(c.t); by = p -> p.first.key)
        length(m.fs) == 1 || continue
        a, e = m.fs[1]
        pw = param_of(a)
        pw === nothing && continue
        p, how = pw
        r = subS(c, monoS(m, k))
        hasleaf(r, p.key) && continue
        how === :id && isempty(r.t) && e > 0 && return p.key => zeroS()
        isone(e) || continue
        return p.key => param_value(how, scaleS(r, -inv(k)))
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
