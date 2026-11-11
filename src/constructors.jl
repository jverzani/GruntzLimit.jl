# ---------------------------------------------------------------------------
# Constructors of exp, log, trig and abs atoms; substitution
# ---------------------------------------------------------------------------
# --- exp / log / trig constructors -------------------------------------------
# exp of a sum. Constants are pulled out (exp(c) = exp(1)^c) and so are terms
# c*log(y) (= y^c). The remaining non-constant terms are kept together in ONE
# atom exp(u0)^c, with u0 normalised to have coefficient 1 on its first monomial.
# Splitting them into separate exp atoms would destroy cancellations between the
# terms, e.g. exp(t^2 log(sin(1/t)) + t^2 log t) has a bounded argument although
# each term alone diverges.
function mkexp(u::Sum)
    res = oneS()
    rest = Dict{Mono,Q}()
    for (m, c) in u.t
        a1 = length(m.fs) == 1 ? m.fs[1] : nothing
        if isempty(m.fs)
            a = funatom(:exp, Sum[oneS()])
            res = mulS(res, monoS(Mono(Pair{Atom,Q}[a => c]), Q(1)))
        elseif a1 !== nothing && a1.second == 1 && a1.first.kind === :fun && a1.first.head === :log
            res = mulS(res, powS(a1.first.args[1]::Sum, c))     # exp(c*log y) = y^c
        else
            rest[m] = c
        end
    end
    if !isempty(rest)
        c = first(sort!(collect(rest); by = p -> p.first.key)).second
        u0 = Sum(Dict{Mono,Q}(m => v / c for (m, v) in rest))
        a = funatom(:exp, Sum[u0])
        res = mulS(res, monoS(Mono(Pair{Atom,Q}[a => c]), Q(1)))
    end
    res
end

function factorint(n::BigInt)
    f = Pair{BigInt,Int}[]
    p = big(2)
    while p * p <= n && p < 1_000_000
        k = 0
        while n % p == 0
            n ÷= p
            k += 1
        end
        k > 0 && push!(f, p => k)
        p += (p == 2 ? 1 : 2)
    end
    n > 1 && push!(f, n => 1)
    f
end

function lograt(c::Q)
    res = zeroS()
    for (p, k) in factorint(numerator(c))
        res = addS(res, scaleS(atomS(funatom(:log, Sum[constS(p)])), Q(k)))
    end
    for (p, k) in factorint(denominator(c))
        res = subS(res, scaleS(atomS(funatom(:log, Sum[constS(p)])), Q(k)))
    end
    res
end

function logatom(a::Atom)
    if a.kind === :fun && a.head === :exp
        a.args[1]::Sum
    elseif a.kind === :base
        mklog(a.args[1]::Sum)
    else
        atomS(funatom(:log, Sum[atomS(a)]))
    end
end

function mklog(s::Sum)
    isempty(s.t) && throw(GruntzError("log(0)", :undefined))
    length(s.t) == 1 && _defer_domain(first(s.t).first) && return atomS(funatom(:log, Sum[s]))
    require_positive(s)
    if length(s.t) == 1
        m, c = first(s.t)
        negs, grp = Pair{Atom,Q}[], nothing
        if needs_signs(m, c)
            pf = positive_factors(m, c)
            # in the expansion variable w the sign is checked by the series (`logPS`)
            pf === nothing && any(p -> hasw(p.first), m.fs) && return atomS(funatom(:log, Sum[s]))
            pf === nothing && throw(GruntzError("log of a negative number", :undefined))
            c, m, negs, grp = pf
        end
        res = lograt(c)
        for (a, e) in m.fs
            res = addS(res, scaleS(logatom(a), e))
        end
        for (a, e) in negs                       # log(a^e) = e log(-a), for a < 0
            res = addS(res, scaleS(atomS(funatom(:log, Sum[negatom(a)])), e))
        end
        grp === nothing || (res = addS(res, atomS(funatom(:log, Sum[grp]))))
        return res
    end
    atomS(funatom(:log, Sum[s]))
end

const PI_ATOM = leafatom(π)

# q for a constant q*π, q rational; otherwise nothing
function piratio(s::Sum)
    length(s.t) == 1 || return nothing
    m, c = first(s.t)
    (length(m.fs) == 1 && m.fs[1].first == PI_ATOM && isone(m.fs[1].second)) ? c : nothing
end

# sin(q*π) exactly, for q with denominator 1, 2, 3, 4 or 6; otherwise nothing
function sinpi_exact(q::Q)
    r = mod(q, 2)
    sg = r >= 1 ? -1 : 1               # sin(π + t) = -sin(t)
    r >= 1 && (r -= 1)
    r > 1//2 && (r = 1 - r)            # sin(π - t) = sin(t)
    half = Q(1) // 2
    v = iszero(r) ? zeroS() : r == half ? oneS() : r == Q(1) // 6 ? constS(half) :
        r == Q(1) // 4 ? scaleS(powS(constS(2), half), half) :
        r == Q(1) // 3 ? scaleS(powS(constS(3), half), half) : nothing
    v === nothing ? nothing : scaleS(v, Q(sg))
end

# sin and cos of a rational multiple of π with a small denominator are evaluated,
# so that zeros such as cos(π/2) are recognised
function mksin(s::Sum)
    isempty(s.t) && return zeroS()
    q = piratio(s)
    v = q === nothing ? nothing : sinpi_exact(q)
    v === nothing ? trigatom(:sin, s) : v
end
function mkcos(s::Sum)
    isempty(s.t) && return oneS()
    q = piratio(s)
    v = q === nothing ? nothing : sinpi_exact(q + Q(1) // 2)   # cos(t) = sin(t + π/2)
    v === nothing ? trigatom(:cos, s) : v
end

# A sin or cos atom, its argument normalised to u + r*π with 0 <= r < 1/2 and the first
# monomial of u with a positive coefficient: the parity and the shifts by multiples of
# π/2 are taken out. Otherwise cos(2t + π) - cos(2t - π), which is 0, is not recognised
# as zero (and its series cancel to every order).
const PI_MONO = Mono(Pair{Atom,Q}[PI_ATOM => Q(1)])
function trigatom(h::Symbol, s::Sum)
    q = get(s.t, PI_MONO, zero(Q))
    u = Sum(Dict{Mono,Q}(m => c for (m, c) in s.t if m != PI_MONO))
    sg = 1
    if !isempty(u.t) && first(sort!(collect(u.t); by = p -> p.first.key)).second < 0
        u, q = negS(u), -q                       # sin(-t) = -sin(t), cos(-t) = cos(t)
        h === :sin && (sg = -sg)
    end
    r = mod(q, 2)
    k = floor(Int, 2r)
    r -= Q(k) // 2
    for _ in 1:k                                 # sin(t + π/2) = cos(t), cos(t + π/2) = -sin(t)
        h === :cos && (sg = -sg)
        h = h === :sin ? :cos : :sin
    end
    if iszero(r) && length(u.t) == 1 && isone(first(u.t).second)
        m = first(u.t).first
        if length(m.fs) == 1 && isone(m.fs[1].second) && m.fs[1].first.kind === :fun &&
           m.fs[1].first.head === :atan
            sc = sincos_atan(m.fs[1].first.args[1]::Sum)
            return scaleS(h === :sin ? sc[1] : sc[2], Q(sg))
        end
    end
    arg = iszero(r) ? u : addS(u, scaleS(atomS(PI_ATOM), r))
    scaleS(atomS(funatom(h, Sum[arg])), Q(sg))
end

# (sin, cos) of atan(s): s/√(1 + s²), 1/√(1 + s²). For s = v/√(1 - v²), as asin(v) and
# acos(v) are written, v and √(1 - v²), so that cos(acos(c)) - c is recognised as 0.
function sincos_atan(s::Sum)
    half = Q(1) // 2
    if length(s.t) == 1
        m, c = first(s.t)
        for (a, e) in m.fs
            (a.kind === :base && e == -half) || continue
            v = mulS(s, powS(atomS(a), half))
            B = a.args[1]::Sum
            skey(B) == skey(subS(oneS(), mulS(v, v))) && return v, powS(B, half)
        end
    end
    # s² = r rational: s √(1/(1 + r)), √(1/(1 + r)), the radical of a rational taken
    # anew, so that it meets the one in s (atan(3/8 √(8/9)) from asin(1/3): sin is 1/3)
    r = ratconst(mulS(s, s))
    if r !== nothing
        c = powS(constS(1 / (1 + r)), half)
        return mulS(s, c), c
    end
    ic = powS(addS(oneS(), mulS(s, s)), -half)
    mulS(s, ic), ic
end

# atan is odd: pull a negative sign of a single-term argument outside
function mkatan(s::Sum)
    isempty(s.t) && return zeroS()
    if length(s.t) == 1 && first(s.t).second < 0
        return negS(mkatan(negS(s)))
    end
    atomS(funatom(:atan, Sum[s]))
end

# erf is odd, as atan is. erfs(u) = exp(u^2) erfc(u) is the tractable part of erf(u)
# for u -> +oo (see `resolve_piecewise`); it is never built from the input.
function mkerf(s::Sum)
    isempty(s.t) && return zeroS()
    if length(s.t) == 1 && first(s.t).second < 0
        return negS(mkerf(negS(s)))
    end
    atomS(funatom(:erf, Sum[s]))
end
mkerfs(s::Sum) = atomS(funatom(:erfs, Sum[s]))

# Odd functions, as erf: sinint, erfi and dawson. cosint is not (complex for a
# negative argument). For u -> +oo, sinint(u) = π/2 - fsi(u) cos(u) - gsi(u) sin(u),
# cosint(u) = fsi(u) sin(u) - gsi(u) cos(u), and erfi(u) = 2/sqrt(π) exp(u^2) dawson(u),
# fsi, gsi and dawson having asymptotic series (see `resolve_piecewise`); fsi and gsi
# are never built from the input.
function mkodd(h::Symbol, s::Sum)
    isempty(s.t) && return zeroS()
    length(s.t) == 1 && first(s.t).second < 0 && return negS(mkodd(h, negS(s)))
    atomS(funatom(h, Sum[s]))
end
function mkcosint(s::Sum)
    isempty(s.t) && throw(GruntzError("cosint has a singularity at 0", :undefined))
    atomS(funatom(:cosint, Sum[s]))
end
mkaux(h::Symbol, s::Sum) = atomS(funatom(h, Sum[s]))

# Clausen's function Cl₂(θ) = -∫₀^θ log|2 sin(t/2)| dt = Σ sin(kθ)/k², odd and 2π-periodic,
# continuous on ℝ, with Cl₂(kπ) = 0. A rational multiple of π is reduced to (-π, π].
function mkclausen2(s::Sum)
    q = pi_multiple(s)
    if q !== nothing
        q = q - 2 * floor((q + 1) // 2)              # in (-1, 1]
        isinteger(q) && return zeroS()
        s = scaleS(atomS(PI_ATOM), q)
    end
    mkodd(:clausen2, s)
end

# binomial(a, b) = gamma(a + 1)/(gamma(b + 1) gamma(a - b + 1)). When b, or a - b, is an
# integer constant k (at most MAX_GAMMA_SHIFT), the polynomial a (a - 1)...(a - k + 1)/k!,
# zero for k < 0.
function mkbinomial(a::Sum, b::Sum)
    for k in (ratconst(b), ratconst(subS(a, b)))
        (k !== nothing && isinteger(k) && k <= MAX_GAMMA_SHIFT) || continue
        k < 0 && return zeroS()
        p = foldl((acc, j) -> mulS(acc, subS(a, constS(Q(j)))), 0:Int(k)-1; init = oneS())
        return scaleS(p, inv(Q(factorial(big(Int(k))))))
    end
    g(s) = mkgamma(addS(s, oneS()))
    mulS(g(a), powS(mulS(g(b), g(subS(a, b))), Q(-1)))
end

# The upper incomplete gamma function gamma(s, z) = ∫_z^∞ t^(s-1) exp(-t) dt, stored as
# funatom(:uigamma, [s, z]). gamma(s, 0) = gamma(s), gamma(1, z) = exp(-z). Its limits
# are taken for s -> +oo with z constant, or z -> +oo with s constant (see
# `resolve_uigamma`).
function mkuigamma(s::Sum, z::Sum)
    ratconst(z) == 0 && return mkgamma(s)
    ratconst(s) == 1 && return mkexp(negS(z))
    atomS(funatom(:uigamma, Sum[s, z]))
end

# The dilogarithm li2(u) = -∫₀^u log(1 - t)/t dt = Σ u^k/k² (SymPy's polylog(2, u)), real
# for u <= 1. Its values at 0, ±1 and 1/2 are known.
function mkli2(s::Sum)
    r = ratconst(s)
    p2 = powS(atomS(PI_ATOM), Q(2))
    r == 0 && return zeroS()
    r == 1 && return scaleS(p2, Q(1) // 6)
    r == -1 && return scaleS(p2, -Q(1) // 12)
    r == Q(1) // 2 && return subS(scaleS(p2, Q(1) // 12), scaleS(powS(mklog(constS(Q(2))), Q(2)), Q(1) // 2))
    r !== nothing && r > 1 && throw(GruntzError("li2 of a number above 1 is not real", :undefined))
    atomS(funatom(:li2, Sum[s]))
end

# Li_k(u) for k = 0, 1, 2: u/(1 - u), -log(1 - u), li2(u)
mkpolylog(k::Int, u::Sum) = k == 2 ? mkli2(u) : k == 1 ? negS(mklog(subS(oneS(), u))) :
                                     mulS(u, powS(subS(oneS(), u), Q(-1)))

# q for s = q π, q rational (0 for s = 0), or nothing
function pi_multiple(s::Sum)
    isempty(s.t) && return Q(0)
    length(s.t) == 1 || return nothing
    m, c = first(s.t)
    (length(m.fs) == 1 && m.fs[1].first == PI_ATOM && isone(m.fs[1].second)) ? c : nothing
end

# The exponential integral Ei (SpecialFunctions' expinti), singular at 0. For u -> ±oo,
# Ei(u) = exp(u) eiaux(u), eiaux(u) ~ sum_k k!/u^(k+1) (see `resolve_piecewise`).
function mkexpinti(s::Sum)
    isempty(s.t) && throw(GruntzError("expinti has a singularity at 0", :undefined))
    atomS(funatom(:expinti, Sum[s]))
end

# The modified Bessel function besselk(ν, u), for a rational order ν, stored with the
# argument first: funatom(:besselk, [u, ν]). K_(-ν) = K_ν. For u -> +oo,
# K_ν(u) = sqrt(π/(2u)) exp(-u) kaux_ν(u), kaux having Hankel's asymptotic series.
function mkbesselk(ν::Sum, s::Sum)
    r = ratconst(ν)
    r === nothing && throw(GruntzError("besselk is supported only for a rational order"))
    atomS(funatom(:besselk, Sum[s, constS(abs(r))]))
end
mkkaux(s::Sum, ν::Sum) = atomS(funatom(:kaux, Sum[s, ν]))

# The modified Bessel function besseli(ν, u), for a rational order ν, stored as besselk
# is. I_(-n) = I_n for an integer n. For u -> +oo, I_ν(u) = exp(u)/sqrt(2πu) iaux_ν(u).
function mkbesseli(ν::Sum, s::Sum)
    r = ratconst(ν)
    r === nothing && throw(GruntzError("besseli is supported only for a rational order"))
    atomS(funatom(:besseli, Sum[s, constS(isinteger(r) ? abs(r) : r)]))
end
mkiaux(s::Sum, ν::Sum) = atomS(funatom(:iaux, Sum[s, ν]))
# besselj(ν, s), stored with the argument first; J_(-n) = (-1)^n J_n for an integer
# order. jred(s, ν) = J_ν(s) (s/2)^(-ν), entire in s (see `jredPS`).
function mkbesselj(ν::Sum, s::Sum)
    r = ratconst(ν)
    if r !== nothing && isinteger(r) && r < 0
        return scaleS(mkbesselj(constS(-r), s), Q(isodd(numerator(r)) ? -1 : 1))
    end
    atomS(funatom(:besselj, Sum[s, ν]))
end
mkjred(s::Sum, ν::Sum) = atomS(funatom(:jred, Sum[s, ν]))

# gamma. Of a positive integer, evaluated; a pole is an error. An argument with the
# limit variable is shifted by an integer to u + r, 0 <= r < 1, the first monomial of
# u with a positive coefficient: gamma(u + r + n) = (u + r)(u + r + 1)...(u + r + n - 1)
# gamma(u + r), so that ratios such as gamma(x + 2)/gamma(x) cancel to polynomials
# before any asymptotic expansion. lgrem(u) is the remainder of Stirling's series,
# log(gamma(u)) - (u - 1/2) log(u) + u - log(2π)/2, for u -> +oo (see
# `resolve_gamma`); it is never built from the input.
const MAX_GAMMA_SHIFT = 64
function mkgamma(s::Sum)
    r = ratconst(s)
    if r !== nothing && isinteger(r)
        r <= 0 && throw(GruntzError("gamma has a pole at $(r)", :undefined))
        r <= 1000 && return constS(factorial(big(numerator(r)) - 1))
    end
    if r !== nothing && denominator(r) == 2 && abs(r) <= 1000   # Γ(1/2 + m) from Γ(1/2) = sqrt(π)
        m = Int(r - Q(1) // 2)
        k = m >= 0 ? prod((Q(1) // 2 + j for j in 0:m-1); init = Q(1)) :
                     inv(prod((Q(1) // 2 + j for j in m:-1); init = Q(1)))
        return scaleS(powS(atomS(PI_ATOM), Q(1) // 2), k)
    end
    c = get(s.t, ONEMONO, zero(Q))
    n = floor(BigInt, c)
    u = Sum(Dict{Mono,Q}(m => v for (m, v) in s.t if m != ONEMONO))
    (iszero(n) || isempty(u.t) || abs(n) > MAX_GAMMA_SHIFT || !hasleaf(u, CONTEXT[].x.key)) &&
        return atomS(funatom(:gamma, Sum[s]))
    b = addS(u, constS(c - n))
    g = atomS(funatom(:gamma, Sum[b]))
    if n > 0
        foldl((acc, j) -> mulS(acc, addS(b, constS(j))), 0:Int(n)-1; init = g)
    else
        foldl((acc, j) -> mulS(acc, powS(subS(b, constS(j)), Q(-1))), 1:Int(-n); init = g)
    end
end
mklgrem(s::Sum) = atomS(funatom(:lgrem, Sum[s]))

# polygamma(k, c), the k-th derivative of digamma, at a constant c, stored with the
# argument first: funatom(:polygamma, [c, k]). At c = 1, ψ(1) = -γ and
# ψ^(k)(1) = (-1)^(k+1) k! ζ(k+1), with ζ(2n) = (-1)^(n+1) B_2n (2π)^(2n) / (2 (2n)!).
function mkpolygamma(k::Int, c::Sum)
    r = ratconst(c)
    # at an integer n > 1, from ψ^(k)(1): ψ^(k)(n) = ψ^(k)(1) + (-1)^k k! sum_(j<n) j^(-k-1)
    if r !== nothing && isinteger(r) && 1 < r <= 64 && (k == 0 || isodd(k))
        s = sum(Q(1) // big(j)^(k + 1) for j in 1:Int(r)-1)
        return addS(mkpolygamma(k, oneS()), constS(Q((-1)^k * factorial(big(k))) * s))
    end
    if r == 1
        k == 0 && return negS(atomS(leafatom(Base.MathConstants.eulergamma)))
        if isodd(k)
            n = (k + 1) ÷ 2
            z = Q((-1)^(n + 1)) * bernoulli(2n) * Q(2)^(2n) / (2 * factorial(big(2n)))
            return scaleS(powS(atomS(PI_ATOM), Q(2n)), Q((-1)^(k + 1) * factorial(big(k))) * z)
        end
    end
    atomS(funatom(:polygamma, Sum[c, constS(Q(k))]))
end
# ψ^(k)(u) for u -> +oo: log(u) + psiaux(u, 0), and psiaux(u, k) for k >= 1, psiaux
# having an asymptotic series in 1/u (see `psiauxPS`)
mkpsiaux(u::Sum, k::Int) = atomS(funatom(:psiaux, Sum[u, constS(Q(k))]))

# lambertw, the principal branch W of the inverse of w exp(w), real for u >= -1/e. Of
# r exp(r), r rational, evaluated (W(0) = 0, W(e) = 1). wexp(L) = W(exp(L)), for
# L -> +oo, is never built from the input (see `resolve_lambertw`).
function mklambertw(s::Sum)
    isempty(s.t) && return zeroS()
    if length(s.t) == 1
        r = first(s.t).second
        skey(s) == skey(scaleS(mkexp(constS(r)), r)) && return constS(r)
    end
    atomS(funatom(:lambertw, Sum[s]))
end
mkwexp(s::Sum) = atomS(funatom(:wexp, Sum[s]))

# abs: |c*m| = |c| * abs(m); sign-normalised so abs(u) and abs(-u) coincide.
# It is eliminated before the limit is computed (see `resolve_piecewise`).
function mkabs(s::Sum)
    isempty(s.t) && return zeroS()
    r = ratconst(s)
    r !== nothing && return constS(abs(r))
    if length(s.t) == 1
        m, c = first(s.t)
        return scaleS(atomS(funatom(:abs, Sum[monoS(m, Q(1))])), abs(c))
    end
    c1 = first(sort!(collect(s.t); by = p -> p.first.key)).second
    atomS(funatom(:abs, Sum[c1 < 0 ? negS(s) : s]))
end

# floor: of a rational constant, evaluated. Otherwise an atom, eliminated before the
# limit is computed (see `resolve_floor`) unless it is a constant with a parameter.
# ceil(u) = -floor(-u).
function mkfloor(s::Sum)
    r = ratconst(s)
    r !== nothing && return constS(floor(r))
    atomS(funatom(:floor, Sum[s]))
end
mkceil(s::Sum) = negS(mkfloor(negS(s)))
mktrunc(s::Sum) = mulS(mksign(s), mkfloor(mkabs(s)))

# cbrt: the real cube root, so cbrt(-8) = -2 (not the principal (-8)^(1/3)): sign(u)
# |u|^(1/3) for a negative constant; a parameter is kept as u^(1/3) (generic). An argument
# in x is an atom, resolved by its limit (see `resolve_cbrt`).
function mkcbrt(s::Sum)
    third = Q(1) // 3
    hasleaf(s, CONTEXT[].x.key) && return atomS(funatom(:cbrt, Sum[s]))
    negconst(s) || return powS(s, third)
    mulS(mksign(s), powS(mkabs(s), third))
end

# sign: sign(c*m) = sign(c) * sign(m), and sign-normalised as abs is, so sign(-u) =
# -sign(u). Eliminated with abs before the limit is computed.
function mksign(s::Sum)
    isempty(s.t) && return zeroS()
    r = ratconst(s)
    r !== nothing && return constS(sign(r))
    if length(s.t) == 1
        m, c = first(s.t)
        return scaleS(atomS(funatom(:sign, Sum[monoS(m, Q(1))])), Q(sign(c)))
    end
    c1 = first(sort!(collect(s.t); by = p -> p.first.key)).second
    c1 < 0 ? negS(atomS(funatom(:sign, Sum[negS(s)]))) : atomS(funatom(:sign, Sum[s]))
end

function mkfun(h::Symbol, a::Vector{Sum})
    h === :exp ? mkexp(a[1]) :
    h === :log ? mklog(a[1]) :
    h === :sin ? mksin(a[1]) :
    h === :atan ? mkatan(a[1]) :
    h === :erf ? mkerf(a[1]) :
    h === :erfs ? mkerfs(a[1]) :
    h === :gamma ? mkgamma(a[1]) :
    h === :lgrem ? mklgrem(a[1]) :
    h === :fracpart ? atomS(funatom(:fracpart, Sum[a[1]])) :
    h in (:erfcxre, :erfcxim, :oscrem, :igs, :igz) ? atomS(funatom(h, a)) :
    h === :uigamma ? mkuigamma(a[1], a[2]) :
    h === :cbrt ? mkcbrt(a[1]) :
    h === :clausen2 ? mkclausen2(a[1]) :
    h === :li2 ? mkli2(a[1]) :
    h === :lambertw ? mklambertw(a[1]) :
    h === :wexp ? mkwexp(a[1]) :
    h in (:sinint, :erfi, :dawson) ? mkodd(h, a[1]) :
    h === :cosint ? mkcosint(a[1]) :
    h in (:fsi, :gsi) ? mkaux(h, a[1]) :
    h === :abs ? mkabs(a[1]) :
    h === :floor ? mkfloor(a[1]) :
    h === :sign ? mksign(a[1]) :
    h === :altsign ? mkaltsign(a[1]) :
    h === :pow ? mkpow(a[1], a[2]) :
    h === :carg ? mkcarg(a[1], a[2]) :
    h === :expinti ? mkexpinti(a[1]) :
    h === :eiaux ? mkaux(h, a[1]) :
    h === :besselk ? mkbesselk(a[2], a[1]) :
    h === :kaux ? mkkaux(a[1], a[2]) :
    h === :besseli ? mkbesseli(a[2], a[1]) :
    h === :iaux ? mkiaux(a[1], a[2]) :
    h === :besselj ? mkbesselj(a[2], a[1]) :
    h === :jred ? mkjred(a[1], a[2]) :
    h === :polygamma ? mkpolygamma(Int(ratconst(a[2])::Q), a[1]) :
    h === :psiaux ? mkpsiaux(a[1], Int(ratconst(a[2])::Q)) :
    h === :cos ? mkcos(a[1]) : throw(GruntzError("unsupported function $h"))
end

function mkpow(a::Sum, b::Sum)
    r = ratconst(b)
    r !== nothing && return powS(a, r)
    negconst(a) && hasleaf(b, CONTEXT[].x.key) && return mulS(mkpow(negS(a), b), mkaltsign(b))
    if negbase(a, b)
        hasleaf(b, CONTEXT[].x.key) && return mulS(mkpow(negS(a), b), mkaltsign(b))
        throw(GruntzError("power of a negative number with a symbolic exponent, which is " *
                          "real only for an integer exponent: write it as (-1)^n (-u)^n", :undefined))
    end
    length(a.t) == 1 && _defer_domain(first(a.t).first) &&
        return atomS(funatom(:pow, Sum[a, b]))          # rebuilt after the substitution
    mkexp(mulS(b, mklog(a)))
end

# whether the base a of a^b (b not a number) is a monomial of x (not of w) that is
# eventually negative: a^b = (-a)^b (-1)^b, which oscillates ((-n/(n + 1))^n) or is not
# real. Decided once x is the variable that tends to +oo (see DEFER_DOMAIN).
function negbase(a::Sum, b::Sum)
    length(a.t) == 1 || return false
    m, c = first(a.t)
    (_defer_domain(m) || any(p -> hasw(p.first), m.fs) || !hasleaf(a, CONTEXT[].x.key)) && return false
    needs_signs(m, c) && positive_factors(m, c) === nothing || return false
    s = try
        sgn(a, CONTEXT[].x)
    catch err
        err isa Union{GruntzError,NeedMorePrecision} || rethrow()
        0
    end
    s < 0
end

# a constant (free of x and of parameters) that is negative
function negconst(a::Sum)
    r = ratconst(a)
    r !== nothing && return r < 0
    hasleaf(a, CONTEXT[].x.key) && return false
    v = try
        numval(a)
    catch err
        err isa FreeSymbol || rethrow()
        return false
    end
    v < 0
end

# altsign(u) = (-1)^u, for u with the limit variable: real only for an integer u. For
# u -> ±oo it is taken to be the sign of a sequence, cos(π u), which oscillates (see
# `resolve_piecewise`); otherwise it is undefined.
mkaltsign(s::Sum) = atomS(funatom(:altsign, Sum[s]))

# --- substitution --------------------------------------------------------------
# B(S)^(-1) N, N a rational multiple r S of S, is r: terms with the factor B(S)^(-1) are
# grouped by their other factors outside the atoms of S, and a group that is r S times
# them is replaced (L/L with L = log(5) - log(2) - log(3), in limits of products of
# powers u^u, SymPy #13332). Atoms' arguments are simplified first.
function cancel_base_inv(s::Sum)::Sum
    s = subs_atoms(s, a -> a.kind === :fun ? mkfun(a.head, Sum[cancel_base_inv(u::Sum) for u in a.args]) : nothing)
    s = merge_const_roots(s)
    for (m, _) in s.t
        for (b, e) in m.fs
            (b.kind === :base && e == -1) || continue
            S = b.args[1]::Sum
            length(S.t) > 1 || continue
            r = cancel_one_base(s, b, S)
            r === nothing || return cancel_base_inv(r)
        end
    end
    s
end

# In each term, powers of positive rational constants with the same denominator in their
# exponents are combined, so that perfect powers come out: sqrt(10) sqrt(3) sqrt(5)
# sqrt(6) = 30
function merge_const_roots(s::Sum)::Sum
    any(m -> count(p -> p.first.kind === :base && (r = ratconst(p.first.args[1]::Sum); r !== nothing && r > 0), m.fs) > 1, keys(s.t)) || return s
    out = zeroS()
    for (m, c) in s.t
        byden = Dict{BigInt,Q}()                     # d => Π c_i^(n_i)
        others = Pair{Atom,Q}[]
        for (a, e) in m.fs
            r = a.kind === :base ? ratconst(a.args[1]::Sum) : nothing
            if r !== nothing && r > 0
                d = denominator(e)
                byden[d] = get(byden, d, Q(1)) * r^numerator(e)
            else
                push!(others, a => e)
            end
        end
        term = monoS(Mono(others), c)
        for (d, v) in byden
            term = mulS(term, powS(constS(v), Q(1) // d))
        end
        out = addS(out, term)
    end
    out
end

function cancel_one_base(s::Sum, b::Atom, S::Sum)
    satoms = Set(a.key for m in keys(S.t) for (a, _) in m.fs)
    groups = Dict{Mono,Sum}()
    rest = zeroS()
    for (m, c) in s.t
        if any(p -> p.first == b && p.second == -1, m.fs)
            k = Mono(filter(p -> p.first != b && !(p.first.key in satoms), m.fs))
            v = monoS(Mono(filter(p -> p.first.key in satoms, m.fs)), c)
            groups[k] = addS(get(groups, k, zeroS()), v)
        else
            rest = addS(rest, monoS(m, c))
        end
    end
    σ0, c0 = first(sort!(collect(S.t); by = p -> p.first.key))
    changed = false
    for (k, v) in groups
        cv = get(v.t, σ0, nothing)
        if cv !== nothing && skey(v) == skey(scaleS(S, cv / c0))
            rest = addS(rest, monoS(k, cv / c0))
            changed = true
        else
            rest = addS(rest, mulS(monoS(k, Q(1)), mulS(v, powS(atomS(b), Q(-1)))))
        end
    end
    changed ? rest : nothing
end

function subs_atoms(s::Sum, f)::Sum
    res = zeroS()
    for (m, c) in s.t
        term = constS(c)
        for (a, e) in m.fs
            r = f(a)
            r === nothing && (r = rebuild(a, f))
            term = mulS(term, powS(r, e))
        end
        res = addS(res, term)
    end
    res
end
function rebuild(a::Atom, f)
    a.kind === :leaf && return atomS(a)
    a.kind === :base && return subs_atoms(a.args[1]::Sum, f)
    mkfun(a.head, Sum[subs_atoms(u::Sum, f) for u in a.args])
end
