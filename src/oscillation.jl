# ---------------------------------------------------------------------------
# Bounded oscillation
# ---------------------------------------------------------------------------
# Gruntz's algorithm needs every subexpression to have an asymptotic expansion, which
# sin(u) and cos(u) for u -> ±oo, and exp of such, have not. When the algorithm stops at
# one (`OSC_MSG`), the limit may still be decided by bounds, as SymPy does with
# `AccumBounds`. Each subexpression s is rated as
#
#     s = P * (β + o(1))   (x -> +oo),
#
# P free of oscillation (its limit is computed by Gruntz's algorithm), β bounded with
# its limit points in the interval [lo, hi]; `exact` when they fill it. β = 1 when
# there is no interval (`iv === nothing`). Then P -> 0 gives 0, and P -> ±oo gives ±oo
# when the interval has one sign. Sums keep their dominant terms (x + 2cos(x) ~ x), the
# ratios of the terms to one another decided by Gruntz's algorithm.
#
# The limit points of a continuous function of s/P are the image of those of β, so
# `exact` survives continuous maps of one quantity (powers, exp, affine combinations);
# products and sums of two bounded quantities are not exact (sin(x) and cos(x) are
# taken to be independent). Intervals are computed in floating point and widened, so
# that a bound that is 0 is never taken for a sign.
struct Iv
    lo::Float64
    hi::Float64
    exact::Bool
end
struct Rated
    P::Sum
    iv::Union{Nothing,Iv}
end

oscfail() = throw(GruntzError(OSC_MSG))
const IV_TOL = 1e-12
const SIGN_TOL = 1e-9     # beyond the widening: a bound that is surely not 0
widen(lo, hi, exact) = Iv(lo - IV_TOL * (1 + abs(lo)), hi + IV_TOL * (1 + abs(hi)), exact)
positive(iv::Iv) = iv.lo > 0
negative(iv::Iv) = iv.hi < 0
onesigned(iv::Iv) = positive(iv) || negative(iv)

function ivmul(a::Union{Nothing,Iv}, b::Union{Nothing,Iv})
    a === nothing && return b
    b === nothing && return a
    ps = (a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi)
    widen(minimum(ps), maximum(ps), false)
end

# [lo, hi]^e, for e an integer or [lo, hi] nonnegative; 0 excluded for e < 0
function ivpow(a::Iv, e::Q)
    e < 0 && !onesigned(a) && oscfail()
    f = Float64(e)
    lo, hi = a.lo^f, a.hi^f
    lo, hi = min(lo, hi), max(lo, hi)
    isinteger(e) && iseven(numerator(e)) && a.lo < 0 < a.hi && (lo = 0.0)
    widen(lo, hi, a.exact)
end

# the value of a constant, or nothing (a parameter)
function float_or_nothing(c::Sum)
    try
        Float64(numval(c))
    catch err
        err isa FreeSymbol || rethrow()
        nothing
    end
end

# Does `a` oscillate, or contain something that does?
function hasosc(a::Atom, x::Atom, memo::Dict{String,Bool})
    get!(memo, a.key) do
        a.kind === :leaf && return false
        hasleaf(a, x.key) || return false
        any(u -> hasosc(u::Sum, x, memo), a.args) && return true
        a.kind === :fun && a.head in (:sin, :cos) && limitinf(a.args[1]::Sum, x) isa Infinity
    end
end
hasosc(s::Sum, x::Atom, memo) = any(m -> any(p -> hasosc(p.first, x, memo), m.fs), keys(s.t))

struct OscRater
    x::Atom
    osc::Dict{String,Bool}
    atoms::Dict{String,Rated}
end
OscRater(x::Atom) = OscRater(x, Dict{String,Bool}(), Dict{String,Rated}())
hasosc(R::OscRater, s) = hasosc(s, R.x, R.osc)
lim(R::OscRater, s::Sum) = limitinf(s, R.x)

function rate(R::OscRater, s::Sum)::Rated
    hasosc(R, s) || return Rated(s, nothing)
    # terms are grouped by their oscillating factors, whose coefficients are summed
    # exactly: (x^2 f(x) - x) cos(x), not x^2 f(x) cos(x) - x cos(x) bounded apart
    groups = Dict{Mono,Sum}()
    for (m, c) in s.t
        mo = Mono(filter(p -> hasosc(R, p.first), m.fs))
        k = monoS(Mono(filter(p -> !hasosc(R, p.first), m.fs)), c)
        groups[mo] = addS(get(groups, mo, zeroS()), k)
    end
    P0 = get(groups, ONEMONO, zeroS())
    cands = Rated[]
    for (mo, k) in groups
        (mo == ONEMONO || iszero(k)) && continue
        r = rate_mono(R, mo, Q(1))
        push!(cands, Rated(mulS(k, r.P), r.iv))
    end
    sort!(cands; by = r -> skey(r.P))       # a deterministic order
    iszero(P0) || pushfirst!(cands, Rated(P0, nothing))
    length(cands) == 1 && return cands[1]
    # the dominant term D; the others are c D (1 + o(1)) with c finite
    D = cands[1].P
    for r in cands[2:end]
        lim(R, mulS(r.P, powS(D, Q(-1)))) isa Infinity && (D = r.P)
    end
    iD = powS(D, Q(-1))
    same = Tuple{Float64,Rated}[]
    for r in cands
        c = lim(R, mulS(r.P, iD))
        c isa Infinity && oscfail()
        numzero(c, R.x) && continue
        v = float_or_nothing(c)
        v === nothing && oscfail()
        push!(same, (v, r))
    end
    if all(p -> p[2].iv === nothing, same)
        # several terms P_j (1 + o(1)) of the same order may cancel to a lower order
        length(same) == 1 && return same[1][2]
        t = sum(first, same)
        abs(t) > IV_TOL * sum(p -> abs(p[1]), same) || oscfail()
        return Rated(foldl(addS, (p[2].P for p in same); init = zeroS()), nothing)
    end
    lo = hi = 0.0
    for (v, r) in same
        a, b = r.iv === nothing ? (1.0, 1.0) : (r.iv.lo, r.iv.hi)
        lo += min(v * a, v * b)
        hi += max(v * a, v * b)
    end
    nb = count(p -> p[2].iv !== nothing, same)
    exact = nb == 1 && any(p -> p[2].iv !== nothing && p[2].iv.exact, same)
    Rated(D, widen(lo, hi, exact))
end

function rate_mono(R::OscRater, m::Mono, c::Q)
    P = constS(c)
    iv = nothing
    for (a, e) in m.fs
        r = rate_pow(rate_atom(R, a), e)
        P = mulS(P, r.P)
        iv = iv === nothing ? r.iv : ivmul(iv, r.iv)
    end
    Rated(P, iv)
end

function rate_pow(r::Rated, e::Q)
    isone(e) && return r
    iv = r.iv
    iv === nothing && return Rated(powS(r.P, e), nothing)
    isinteger(e) && return Rated(powS(r.P, e), ivpow(iv, e))
    # a fractional power: β nonnegative, or nonpositive (a bound 0 is widened: clamped)
    if iv.lo > -SIGN_TOL
        Rated(powS(r.P, e), ivpow(Iv(max(iv.lo, 0.0), iv.hi, iv.exact), e))
    elseif iv.hi < SIGN_TOL
        Rated(powS(negS(r.P), e), ivpow(Iv(max(-iv.hi, 0.0), -iv.lo, iv.exact), e))
    else
        oscfail()
    end
end

function rate_atom(R::OscRater, a::Atom)::Rated
    hasosc(R, a) || return Rated(atomS(a), nothing)
    get!(R.atoms, a.key) do
        a.kind === :base && return rate(R, a.args[1]::Sum)
        a.kind === :fun || oscfail()
        u = a.args[1]::Sum
        a.head in (:sin, :cos) && return Rated(oneS(), Iv(-1.0, 1.0, diverges(R, u)))
        a.head === :exp && return rate_exp(R, u)
        a.head === :log && return rate_log(R, u)
        oscfail()
    end
end

# u -> ±oo: sin(u) and cos(u) then take every value in [-1, 1] infinitely often
function diverges(R::OscRater, u::Sum)
    hasosc(R, u) || return true             # an oscillating sin or cos: u -> ±oo
    r = rate(R, u)
    lim(R, r.P) isa Infinity && (r.iv === nothing || onesigned(r.iv))
end

# exp(U0 + O), U0 the terms free of oscillation and O = P (β + o(1)) the others, rated
# together (so that they may cancel): P tends to a finite limit L, and O to the
# interval L [lo, hi]
function rate_exp(R::OscRater, u::Sum)
    U0, O = zeroS(), zeroS()
    for (m, c) in u.t
        any(p -> hasosc(R, p.first), m.fs) ? (O = addS(O, monoS(m, c))) : (U0 = addS(U0, monoS(m, c)))
    end
    r = rate(R, O)
    L = lim(R, r.P)
    L isa Infinity && oscfail()
    numzero(L, R.x) && return Rated(mkexp(U0), nothing)
    v = float_or_nothing(L)
    v === nothing && oscfail()
    a, b = r.iv === nothing ? (1.0, 1.0) : (r.iv.lo, r.iv.hi)
    Rated(mkexp(U0), widen(exp(min(v * a, v * b)), exp(max(v * a, v * b)), r.iv === nothing || r.iv.exact))
end

# log(P (β + o(1))) = log(P) + log(β) + o(1)
function rate_log(R::OscRater, u::Sum)
    r = rate(R, u)
    iv = r.iv
    iv === nothing || positive(iv) || oscfail()
    lP = mklog(r.P)
    L = lim(R, lP)
    L isa Infinity && return Rated(lP, nothing)
    if iv === nothing
        numzero(L, R.x) && oscfail()
        return Rated(lP, nothing)
    end
    v = float_or_nothing(L)
    v === nothing && oscfail()
    Rated(oneS(), widen(v + log(iv.lo), v + log(iv.hi), iv.exact))
end

# The limit of e, x -> +oo, where Gruntz's algorithm met an oscillating subexpression
function bounded_limit(e::Sum, x::Atom)
    R = OscRater(x)
    r = rate(R, e)
    L = lim(R, r.P)
    iv = r.iv
    iv === nothing && return L
    nolimit = GruntzError("the limit does not exist: the expression oscillates", :nolimit)
    if L isa Infinity
        positive(iv) && return L
        negative(iv) && return Infinity(-signof(L))
        # β near +1 and -1 infinitely often; not when it only touches 0, as then the
        # o(1) can decide (x (1 - cos(x)) + sqrt(x) -> oo)
        iv.exact && iv.lo < -SIGN_TOL && iv.hi > SIGN_TOL && throw(nolimit)
    else
        numzero(L, x) && return zeroS()
        iv.exact && iv.hi - iv.lo > SIGN_TOL && throw(nolimit)
    end
    oscfail()
end
