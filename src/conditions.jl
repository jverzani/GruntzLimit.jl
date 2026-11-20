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


ineqs(cd::Cond, vars::Dict{String,Mono}) = cond_ineqs(cd.c, cd.rel, vars)
# c rel 0, and a condition on a log of a parameter also as one on the parameter (see
# `delog`): log(b) - log(a) >= 0 also as b - a >= 0
function cond_ineqs(c::Sum, rel::Symbol, vars::Dict{String,Mono})
    out = ineqs(c, rel, vars)
    dl = delog(c)
    dl === nothing || append!(out, ineqs(dl[1], dl[2] < 0 ? flip(rel) : rel, vars))
    out
end
function ineqs(c::Sum, rel::Symbol, vars::Dict{String,Mono})
    a, k = linform(c, vars)
    rel === :> ? [Ineq(a, k, true)] :
    rel === :< ? [Ineq(negate(a), -k, true)] :
    rel === :>= ? [Ineq(a, k, false)] :
    rel === :<= ? [Ineq(negate(a), -k, false)] :
    rel === :(==) ? [Ineq(a, k, false), Ineq(negate(a), -k, false)] : Ineq[]
end

# c = k log(±p) + r, r free of the parameter p, has the sign of σ (p - v) with
# v = ±exp(-r/k), log being increasing: (p - v, σ), or nothing. log(b) - log(a) has the
# sign of b - a, log(a) - 1 that of a - exp(1), 2log(a) - log(b) that of a - sqrt(b).
function delog(c::Sum)
    for (m, k) in sort!(collect(c.t); by = p -> p.first.key)
        (length(m.fs) == 1 && isone(m.fs[1].second)) || continue
        pw = param_of(m.fs[1].first)
        (pw === nothing || pw[2] === :id) && continue
        p, how = pw
        r = subS(c, monoS(m, k))
        hasleaf(r, p.key) && continue
        v = try
            param_value(how, scaleS(r, -inv(k)))
        catch err
            err isa GruntzError || rethrow()
            continue
        end
        return subS(atomS(p), v), (k < 0) ⊻ (how === :neglog) ? -1 : 1
    end
    nothing
end

# The sign of an atom with parameters, from the context (linear reasoning only):
# ±1 or nothing. log(s) has the sign of s - 1, sign(s) that of s; abs is taken to be positive (a zero
# argument is split off as a case of its own). erf(s) has the sign of s, erfs is positive,
# as are lgrem, fsi and gsi (their arguments tend to +oo) and gamma of a positive number.
# sinint, erfi and dawson have the sign of their argument, as has li2 (real for u <= 1).
function atom_sign(a::Atom)
    a.kind === :fun && a.head in (:exp, :abs, :erfs, :lgrem, :fsi, :gsi, :airyp, :airyr) && return 1
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
# can hold together. The logs of parameters in the conditions `domain` are taken to be
# real: log(p) needs p > 0, log(-p) needs p < 0 (for merging cases; only those of the
# conditions assumed, not of one tested, which would be implied vacuously)
const SAT_CACHE = ScopedValue{Union{Nothing,Dict{String,Bool}}}(nothing)   # see `merge_cases`
condkey(l::Vector{Tuple{Sum,Symbol}}) = join(sort!(["$(skey(c)) $rel" for (c, rel) in l]), "; ")
function satisfiable(clist::Vector{Tuple{Sum,Symbol}}; domain = nothing)
    cache = SAT_CACHE[]
    cache === nothing && return _satisfiable(clist, domain)
    get!(() -> _satisfiable(clist, domain), cache, condkey(clist) * " | " * (domain === nothing ? "-" : condkey(domain)))
end
function _satisfiable(clist::Vector{Tuple{Sum,Symbol}}, domain)
    i = findfirst(l -> l[2] === :!=, clist)
    if i !== nothing
        c, rest = clist[i][1], deleteat!(copy(clist), i)
        return satisfiable(push!(copy(rest), (c, :<)); domain) || satisfiable(push!(rest, (c, :>)); domain)
    end
    vars = Dict{String,Mono}()
    base = Ineq[]
    for cd in CONTEXT[].conds
        append!(base, ineqs(cd, vars))
    end
    # the conditions assumed, with their logs' domains
    assumed = domain === nothing ? Tuple{Sum,Symbol}[] : [domain; domain_conds(domain)]
    for (c, rel) in assumed
        append!(base, ineqs(c, rel, vars))
    end
    # a condition on logs is also read without them (`delog`) only where they are real:
    # where the assumed conditions imply its logs' domains (p > 0 for log(p))
    holds = Dict{Tuple{String,Symbol},Bool}()
    known(l) = get!(holds, (skey(l[1]), l[2])) do
        !isempty(assumed) && !satisfiable(push!(copy(assumed), (l[1], l[2] === :> ? :<= : :>=)))
    end
    for (c, rel) in clist
        dl = domain_conds([(c, rel)])
        real = !isempty(dl) && all(known, dl)
        append!(base, real ? cond_ineqs(c, rel, vars) : ineqs(c, rel, vars))
    end
    feasible(append!(base, fact_ineqs(vars)))
end

# p > 0 for each log(p) of a parameter p in the conditions (p < 0 for log(-p))
function domain_conds(conds::Vector{Tuple{Sum,Symbol}})
    out = Tuple{Sum,Symbol}[]
    for (c, _) in conds, m in keys(c.t), (a, _) in m.fs
        pw = param_of(a)
        (pw === nothing || pw[2] === :id) && continue
        push!(out, (atomS(pw[1]), pw[2] === :log ? :> : :<))
    end
    unique(l -> (skey(l[1]), l[2]), out)
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
    s2 = ratsimp(s)            # a rational function in lowest terms (see `ratsimp`)
    skey(s2) == skey(s) || return possible_signs(s2; facts = facts)
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
    # Fourier-Motzkin takes the powers of a parameter as unrelated (a and a^2): a
    # polynomial in one parameter is decided on the parameter's interval (`poly_signs`)
    if length(out) > 1
        ps = poly_signs(s)
        ps === nothing || isempty(intersect(out, ps)) || (out = intersect(out, ps))
    end
    # and takes log(p) and p as unrelated: a sum k log(p) + r is decided as p - exp(-r/k)
    if length(out) > 1
        dl = delog(s)
        if dl !== nothing
            ps = possible_signs(dl[1])
            dl[2] < 0 && (ps = sort!(-ps))
            isempty(intersect(out, ps)) || (out = intersect(out, ps))
        end
    end
    out
end

# ---------------------------------------------------------------------------
# Signs of a polynomial in one parameter
# ---------------------------------------------------------------------------
# A constant that is a polynomial in a single parameter p, with rational coefficients,
# has its signs on the interval for p given by the conditions of the context that are
# linear in p alone (a > 1, 2a - 3 <= 0): roots at the ends are divided out, and the
# real roots inside are counted with Sturm's sequence, in exact arithmetic. With none
# inside, the sign there is that at one point. 1 - a^2 < 0 for a > 1.

# (p, coefficients from degree 0 up), or nothing
function univariate_poly(s::Sum)
    p = nothing
    for m in keys(s.t), (a, e) in m.fs
        (a.kind === :leaf && isone(denominator(e)) && e > 0 && numval_or_nothing(a) === nothing) ||
            return nothing
        p === nothing ? (p = a) : (p.key == a.key || return nothing)
    end
    p === nothing && return nothing
    deg(m) = isempty(m.fs) ? 0 : Int(numerator(m.fs[1].second))
    cs = zeros(Q, maximum(deg, keys(s.t)) + 1)
    for (m, c) in s.t
        cs[deg(m)+1] += c
    end
    p, cs
end

ptrim!(P::Vector{Q}) = (while length(P) > 1 && iszero(P[end]); pop!(P); end; P)
function peval(P::Vector{Q}, t::Q)
    acc = zero(Q)
    for c in Iterators.reverse(P)
        acc = acc * t + c
    end
    acc
end
pderiv(P::Vector{Q}) = length(P) == 1 ? [zero(Q)] : [P[i] * (i - 1) for i in 2:length(P)]
function prem(A::Vector{Q}, B::Vector{Q})
    r = copy(A)
    while length(r) >= length(B)
        f = r[end] / B[end]
        sh = length(r) - length(B)
        for i in eachindex(B)
            r[i+sh] -= f * B[i]
        end
        pop!(r)
        isempty(r) && return [zero(Q)]
    end
    ptrim!(r)
end
# P(t) = (t - r) q(t) + P(r)
function deflate(P::Vector{Q}, r::Q)
    n = length(P) - 1
    q = zeros(Q, n)
    acc = zero(Q)
    for i in n:-1:1
        acc = acc * r + P[i+1]
        q[i] = acc
    end
    q
end
function sturm(P::Vector{Q})
    seq = [P, pderiv(P)]
    while !(length(seq[end]) == 1 && iszero(seq[end][1]))
        push!(seq, -prem(seq[end-1], seq[end]))
    end
    pop!(seq)
    seq
end
# sign changes of the sequence at t, a rational or ±Inf (nothing for -oo / +oo by `side`)
function variations(seq, t::Union{Q,Nothing}, side::Int)
    sg = Int[]
    for P in seq
        v = t === nothing ? sign(P[end]) * (side < 0 && isodd(length(P) - 1) ? -1 : 1) : sign(peval(P, t))
        iszero(v) || push!(sg, Int(v))
    end
    count(i -> sg[i] != sg[i+1], 1:length(sg)-1)
end

# the interval for p from the conditions linear in p alone: (lo, lo strict, hi, hi strict)
function param_interval(p::Atom)
    lo, los, hi, his = nothing, false, nothing, false
    lower(v, st) = (lo === nothing || v > lo || (v == lo && st)) && ((lo, los) = (v, st))
    upper(v, st) = (hi === nothing || v < hi || (v == hi && st)) && ((hi, his) = (v, st))
    for cd in CONTEXT[].conds
        up = univariate_poly(cd.c)
        (up === nothing || up[1].key != p.key || length(ptrim!(up[2])) != 2) && continue
        c0, c1 = up[2]
        v = -c0 / c1
        rel = c1 > 0 ? cd.rel : get(Dict(:> => :<, :>= => :<=, :< => :>, :<= => :>=), cd.rel, cd.rel)
        rel in (:>, :>=, :(==)) && lower(v, rel === :>)
        rel in (:<, :<=, :(==)) && upper(v, rel === :<)
    end
    lo, los, hi, his
end

# The rational roots of P, increasing, by the rational root theorem (r = ±u/v, u
# dividing the lowest nonzero coefficient and v the highest, of P with integer
# coefficients); none sought when those exceed 10^8
function rational_roots(P::Vector{Q})
    d = lcm(denominator.(P))
    A = [numerator(c * d) for c in P]
    roots = Q[]
    if iszero(A[1])
        push!(roots, zero(Q))
        while length(A) > 1 && iszero(A[1])
            popfirst!(A)
        end
    end
    length(A) == 1 && return roots
    a0, an = abs(A[1]), abs(A[end])
    (a0 > 10^8 || an > 10^8) && return roots
    divisors(n) = (ds = [k for k in 1:isqrt(n) if n % k == 0]; unique!([ds; [n ÷ k for k in ds]]))
    for v in divisors(an), u in divisors(a0), σ in (1, -1)
        r = Q(σ * u, v)
        iszero(peval(P, r)) && push!(roots, r)
    end
    sort!(unique!(roots))
end

# the possible signs of s, a polynomial in one parameter, or nothing
function poly_signs(s::Sum)
    up = univariate_poly(s)
    up === nothing && return nothing
    p, P = up
    length(ptrim!(P)) < 2 && return nothing
    lo, los, hi, his = param_interval(p)
    if lo !== nothing && hi !== nothing
        lo > hi && return nothing
        lo == hi && return (los || his) ? nothing : [Int(sign(peval(P, lo)))]
    end
    out = Int[]
    R, jh = copy(P), 0
    if lo !== nothing
        los || push!(out, Int(sign(peval(P, lo))))
        while length(R) > 1 && iszero(peval(R, lo))
            R = deflate(R, lo)
        end
    end
    if hi !== nothing
        his || push!(out, Int(sign(peval(P, hi))))
        while length(R) > 1 && iszero(peval(R, hi))
            R, jh = deflate(R, hi), jh + 1
        end
    end
    if length(R) > 1
        seq = sturm(R)
        variations(seq, lo, -1) - variations(seq, hi, 1) > 0 && return nothing
    end
    # no root inside: the sign at one point, with (t - lo)^j > 0 and (t - hi)^j of sign (-1)^j
    t = lo !== nothing && hi !== nothing ? (lo + hi) / 2 : lo !== nothing ? lo + 1 : hi !== nothing ? hi - 1 : zero(Q)
    push!(out, Int(sign(peval(R, t))) * (isodd(jh) ? -1 : 1))
    sort!(unique!(out))
end

# c times a product of exp atoms, π and powers of positive rational constants: never
# zero, however small (exp(-x) at x = 1000 is below the numeric zero test)
function positive_mono(s::Sum)
    length(s.t) == 1 || return false
    m = first(keys(s.t))
    all(m.fs) do (a, _)
        a === PI_ATOM || (a.kind === :fun && a.head === :exp) ||
            (a.kind === :base && (r = ratconst(a.args[1]::Sum); r !== nothing && r > 0))
    end
end

# The constant s, free of x, as N * prod(d_i^-k_i): the integer powers of sums d_i in it
# (bases, nonzero where s is defined) multiplied out of the denominators, and N expanded,
# with cos(u)^2 written 1 - sin(u)^2 and the exps of each term merged, exp(a)^p exp(b)^q =
# exp(p a + q b) (so exp(A - B)^-1 = exp(A)^-1 exp(B), SymPy #5172). Returns (N, Dict(key => (d_i atom, k_i))), or
# nothing when there is nothing to do or N grows too large.
function rational_form(s::Sum)
    length(s.t) < 2 && return nothing
    any(m -> any(p -> hasvar(p.first), m.fs), keys(s.t)) && return nothing
    low = Dict{String,Tuple{Atom,Q}}()
    frac = Set{String}()
    trig = false
    exps = any(m -> count(p -> p.first.kind === :fun && p.first.head === :exp, m.fs) >= 2, keys(s.t))
    for m in keys(s.t), (a, e) in m.fs
        if a.kind === :base
            isone(denominator(e)) || push!(frac, a.key)
            low[a.key] = (a, min(e, get(low, a.key, (a, e))[2]))
        elseif a.kind === :fun && a.head === :cos && isinteger(e) && iseven(numerator(e))
            trig = true
        end
    end
    foreach(k -> delete!(low, k), frac)
    (isempty(low) && !trig && !exps) && return nothing
    any(((a, e),) -> e < -8, values(low)) && return nothing
    den = Dict{String,Tuple{Atom,Q}}(k => (a, -e) for (k, (a, e)) in low if e < 0)
    t = isempty(den) ? s : mulS(s, monoS(mono(Dict{Atom,Q}(a => k for (a, k) in values(den))), Q(1)))
    N = zeroS()
    for (m, c) in t.t
        term = constS(c)
        ex = zeroS()                                  # the merged exponent of the exps
        for (a, e) in m.fs
            if exps && a.kind === :fun && a.head === :exp
                ex = addS(ex, scaleS(a.args[1]::Sum, e))
                continue
            end
            f = if haskey(low, a.key) && 0 < e <= 8
                powS(a.args[1]::Sum, e)
            elseif a.kind === :fun && a.head === :cos && isinteger(e) && 0 < e <= 8 && iseven(numerator(e))
                powS(subS(oneS(), powS(mksin(a.args[1]::Sum), Q(2))), e / 2)
            else
                powS(atomS(a), e)
            end
            term = mulS(term, f)
            length(term.t) > 2000 && return nothing
        end
        isempty(ex.t) || (term = mulS(term, mkexp(ex)))
        N = addS(N, term)
    end
    N, den
end

# Whether the constant s vanishes identically as a rational function of its atoms (see
# `rational_form`): (1 + n)^-1 + n (1 + n)^-1 - 1 and sin(a)^2 + cos(a)^2 - 1 are 0 (SymPy
# #6843, #6364), which neither the linear reasoning nor, with a parameter, the numeric
# test sees.
function ident_zero(s::Sum)
    r = rational_form(s)
    r !== nothing && isempty(r[1].t)
end

# s with the denominators of its rational form (see `rational_form`) that are polynomials
# in one parameter cancelled where they divide the numerator, when that is shorter:
# -1 + (1 + n)^-1 (1 + n)^2 - 1/2 (1 + n)^-2 n (1 + n)^2 is n/2 (SymPy #6843)
function ratsimp(s::Sum)::Sum
    r = rational_form(s)
    r === nothing && return s
    N, den = r
    isempty(N.t) && return N
    isempty(den) && return length(N.t) < length(s.t) ? N : s
    out = Pair{Atom,Q}[]
    for (a, k) in values(den)
        d = a.args[1]::Sum
        while k > 0
            q = polydiv_exact(N, d)
            q === nothing && break
            N, k = q, k - 1
        end
        k > 0 && push!(out, a => -k)
    end
    t = isempty(out) ? N : mulS(N, monoS(mono(Dict{Atom,Q}(out)), Q(1)))
    length(t.t) < length(s.t) ? t : s
end

# N / d when d is a polynomial in one parameter p with rational coefficients and N a
# polynomial in p (coefficients free of p) that d divides; otherwise nothing
function polydiv_exact(N::Sum, d::Sum)
    p = nothing
    dc = Dict{Int,Q}()
    for (m, c) in d.t
        if isempty(m.fs)
            dc[0] = c
        elseif length(m.fs) == 1 && isparam(m.fs[1].first) && isinteger(m.fs[1].second) && m.fs[1].second > 0
            a = m.fs[1].first
            p === nothing ? (p = a) : (p == a || return nothing)
            dc[Int(m.fs[1].second)] = c
        else
            return nothing
        end
    end
    (p === nothing || length(dc) < 2) && return nothing
    md = maximum(keys(dc))
    nc = Dict{Int,Sum}()
    for (m, c) in N.t
        e = Q(0)
        rest = Pair{Atom,Q}[]
        for (a, q) in m.fs
            a == p ? (e = q) : push!(rest, a => q)
        end
        (isinteger(e) && e >= 0) || return nothing
        nc[Int(e)] = addS(get(nc, Int(e), zeroS()), monoS(Mono(rest), c))
    end
    filter!(kv -> !isempty(kv.second.t), nc)
    quot = Dict{Int,Sum}()
    while !isempty(nc)
        dn = maximum(keys(nc))
        dn < md && return nothing
        lc = scaleS(nc[dn], inv(dc[md]))
        quot[dn - md] = lc
        for (j, cj) in dc
            k = dn - md + j
            nc[k] = subS(get(nc, k, zeroS()), scaleS(lc, cj))
            isempty(nc[k].t) && delete!(nc, k)
        end
    end
    out = zeroS()
    pa = atomS(p)
    for (j, c) in quot
        out = addS(out, mulS(c, powS(pa, Q(j))))
    end
    out
end

function csign(s::Sum)::Int
    isempty(s.t) && return 0
    r = ratconst(s)
    r !== nothing && return Int(sign(r))
    positive_mono(s) && return Int(sign(first(values(s.t))))
    ident_zero(s) && return 0
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
    positive_mono(s) && return false
    ident_zero(s) && return true
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
    if !any(m -> any(p -> numval_or_nothing(p.first) === nothing, m.fs), keys(k.t))
        # a numeric constant: one that is surely negative (log(-2 + √3), the limit of
        # acosh(u) = log(u + sqrt(u^2 - 1)) at u = -2) is retried on the principal branch
        v = try
            numval(k)
        catch err
            err isa Union{GruntzError,DomainError} || rethrow()
            return
        end
        v < -1e-30 && throw(GruntzError(what == "log" ? "log of a negative number" :
                                        "complex power of a negative number", :undefined))
        return
    end
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
