# ---------------------------------------------------------------------------
# Truncated power series in w
# ---------------------------------------------------------------------------
# Exponents of w are rational, except when comparable exponentials have an
# irrational ratio (e.g. 3^x and 5^x, ratio log(5)/log(3)): then an exponent is
# q + r, r a constant free of x (it may contain a parameter, as for x^a).
# Rational exponents compare exactly; others by the sign of their difference.
struct Ex
    q::Q
    r::Sum                          # zeroS() for a rational exponent
    rkey::String
end
Ex(q::Q) = Ex(q, zeroS(), "0")
Ex(q::Integer) = Ex(Q(q))
function Ex(q::Q, r::Sum)
    rc = ratconst(r)
    rc !== nothing && return Ex(q + rc)
    Ex(q, r, skey(r))
end
israt(a::Ex) = a.rkey == "0"
value(a::Ex) = israt(a) ? BigFloat(numerator(a.q)) / BigFloat(denominator(a.q)) : numval(toS(a))
Base.:(==)(a::Ex, b::Ex) = a.q == b.q && a.rkey == b.rkey
Base.hash(a::Ex, h::UInt) = hash(a.q, hash(a.rkey, h))
Base.:+(a::Ex, b::Ex) = israt(a) && israt(b) ? Ex(a.q + b.q) : Ex(a.q + b.q, addS(a.r, b.r))
Base.:-(a::Ex) = israt(a) ? Ex(-a.q) : Ex(-a.q, negS(a.r))
Base.:-(a::Ex, b::Ex) = a + (-b)
Base.:*(a::Ex, q::Q) = israt(a) ? Ex(a.q * q) : Ex(a.q * q, scaleS(a.r, q))
# The precision marker HUGE (an exact series) dominates any parameter in an exponent
function Base.isless(a::Ex, b::Ex)
    (israt(a) && israt(b)) || abs(a.q - b.q) >= HUGE / 2 ? a.q < b.q :
        (a != b && csign(subS(toS(b), toS(a))) > 0)
end
Base.iszero(a::Ex) = israt(a) && iszero(a.q)
Base.sign(a::Ex) = israt(a) ? Int(sign(a.q)) : csign(toS(a))
toS(a::Ex) = addS(constS(a.q), a.r)
const EX0, EX1, HUGE_EX = Ex(0), Ex(1), Ex(HUGE)

# the leaf w^r for an irrational constant r (see `mrv_leadterm`)
wpowatom(r::Sum) = Atom(:leaf, r, Any[], WLEAF.key * "^(" * skey(r) * ")")
iswleaf(a::Atom) = a.kind === :leaf && startswith(a.key, WLEAF.key)
hasw(a::Atom) = iswleaf(a) || (a.kind !== :leaf && any(u -> any(m -> any(p -> hasw(p.first), m.fs), keys((u::Sum).t)), a.args))

# The precision of a series: exact for exponents below every bound. Bounds whose
# order the context does not decide (4 and 3a) are kept side by side, and a term is
# kept only when it is decidably below all of them. Dropping a term is always safe,
# so no case split is asked for.
struct Prec
    bs::Vector{Ex}
end
Prec(e::Ex) = Prec([e])
function safe_lt(a::Ex, b::Ex)
    try
        isless(a, b)
    catch err
        err isa NeedSign || rethrow()
        nothing
    end
end
below(k::Ex, p::Prec) = all(b -> safe_lt(k, b) === true, p.bs)
function pmin(p::Prec, q::Prec)
    bs = unique!([p.bs; q.bs])
    length(bs) == 1 && return Prec(bs)
    Prec([b for b in bs if !any(c -> safe_lt(c, b) === true, bs)])
end
Base.:+(p::Prec, d::Ex) = Prec([b + d for b in p.bs])
Base.:-(p::Prec, d::Ex) = Prec([b - d for b in p.bs])
addprec(p::Prec, q::Prec) = reduce(pmin, [Prec(b + c) for b in p.bs for c in q.bs])
const HUGE_P = Prec(HUGE_EX)
# exact: no bound, or only a shifted HUGE_EX (w^-1 is exact to HUGE - 1)
isexact(p::Prec) = all(b -> iszero(b.r) && b.q > HUGE / 2, p.bs)

struct PS
    c::Dict{Ex,Sum}   # exponent -> nonzero coefficient (an x-expression)
    prec::Prec       # exact for exponents below it
end
val(a::PS) = minimum(keys(a.c))
valp(a::PS) = isempty(a.c) ? a.prec : Prec(val(a))
onePS() = PS(Dict{Ex,Sum}(EX0 => oneS()), HUGE_P)

function trunc_ps(c::Dict{Ex,Sum}, prec::Prec)
    d = Dict{Ex,Sum}()
    for (k, v) in c
        (!isempty(v.t) && below(k, prec)) && (d[k] = v)
    end
    PS(d, prec)
end
function addPS(a::PS, b::PS)
    c = copy(a.c)
    for (k, v) in b.c
        c[k] = haskey(c, k) ? addS(c[k], v) : v
    end
    trunc_ps(c, pmin(a.prec, b.prec))
end
scalePS(a::PS, s::Sum) = trunc_ps(Dict{Ex,Sum}(k => mulS(v, s) for (k, v) in a.c), a.prec)
shiftPS(a::PS, d::Ex) = PS(Dict{Ex,Sum}(k + d => v for (k, v) in a.c), a.prec + d)
function mulPS(a::PS, b::PS)
    prec = pmin(addprec(a.prec, valp(b)), addprec(b.prec, valp(a)))
    c = Dict{Ex,Sum}()
    for (ka, ca) in a.c, (kb, cb) in b.c
        k = ka + kb
        below(k, prec) || continue
        v = mulS(ca, cb)
        c[k] = haskey(c, k) ? addS(c[k], v) : v
    end
    trunc_ps(c, prec)
end

binomq(q::Q, k::Int) = (r = one(Q); for j in 0:k-1; r *= (q - j) // (j + 1); end; r)

const MAX_POLY_TERMS = 64

# sum_{k>=kmin} coef(k) u^k, u having positive valuation; relative target `Trel`.
# A coefficient is a rational or a constant `Sum`.
# A valuation with a parameter (w^a) has no numerical value: a few terms are taken
# and the precision is that of the first one left out.
function polyPS(u::PS, coef, kmin::Int, Trel::Q)
    # u = O(w^p) with no terms: the sum is coef(0) to the order of u (exactly, for u = 0)
    acc = PS(Dict{Ex,Sum}(), isempty(u.c) ? u.prec : pmin(Prec(Ex(Trel)), u.prec))
    v = isempty(u.c) ? EX0 : val(u)
    K = if isempty(u.c)
        kmin
    elseif israt(v)
        k = max(kmin, Int(ceil(BigInt, Trel / v.q)))
        # a tiny valuation (w^(1/10^8), from float exponents) would need very many terms:
        # fewer are taken, and the precision is that of the first one left out
        k > MAX_POLY_TERMS && (k = max(kmin, MAX_POLY_TERMS);
                               acc = PS(acc.c, pmin(acc.prec, Prec(v * Q(k + 1)))))
        k
    else
        vv = try value(v) catch err; err isa FreeSymbol || rethrow(); nothing end
        vv === nothing ? (acc = PS(acc.c, pmin(acc.prec, Prec(v * Q(kmin + 3)))); kmin + 2) :
                         max(kmin, Int(ceil(BigInt, BigFloat(Trel) / vv)))
    end
    pw = onePS()
    for k in 0:K
        if k >= kmin
            ck = coef(k)
            iszero(ck) || (acc = addPS(acc, scalePS(pw, ck isa Sum ? ck : constS(ck))))
        end
        k < K && (pw = mulPS(pw, u))
    end
    acc
end

# a = c0 * w^v * (1 + r); returns (v, c0, r)
function split_lead(a::PS)
    a = dropzeros(a)
    isempty(a.c) && throw(NeedMorePrecision())
    v = val(a)
    c0 = a.c[v]
    ic0 = powS(c0, Q(-1))
    r = PS(Dict{Ex,Sum}(k - v => mulS(cc, ic0) for (k, cc) in a.c if k != v), a.prec - v)
    v, c0, r
end

function powPS(a::PS, q::Q, P::Q)
    q == 1 && return a
    iszero(q) && return onePS()
    v, c0, r = split_lead(a)
    T = polyPS(r, k -> binomq(q, k), 0, P)
    shiftPS(scalePS(T, powS(c0, q)), v * q)
end

const OSC_MSG = "argument of exp/sin/cos diverges (oscillation or essential singularity)"

function const_and_rest(a::PS)
    # terms of negative order that are 0 in the context (exp(c x), c = 0)
    any(k -> k < EX0, keys(a.c)) && (a = dropzeros(a))
    all(b -> EX0 < b, a.prec.bs) || throw(NeedMorePrecision())
    any(k -> k < EX0, keys(a.c)) &&
        throw(GruntzError(OSC_MSG))
    c0 = get(a.c, EX0, zeroS())
    c0, trunc_ps(Dict{Ex,Sum}(k => v for (k, v) in a.c if k != EX0), a.prec)
end

function expPS(a::PS, P::Q)
    c0, u = const_and_rest(a)
    scalePS(polyPS(u, k -> Q(1) // factorial(big(k)), 0, P), mkexp(c0))
end

function trigPS(a::PS, P::Q)
    c0, u = const_and_rest(a)
    su = polyPS(u, k -> iseven(k) ? Q(0) : Q((-1)^((k - 1) ÷ 2)) // factorial(big(k)), 0, P)
    cu = polyPS(u, k -> isodd(k) ? Q(0) : Q((-1)^(k ÷ 2)) // factorial(big(k)), 0, P)
    s0, k0 = mksin(c0), mkcos(c0)
    addPS(scalePS(cu, s0), scalePS(su, k0)), addPS(scalePS(cu, k0), scalePS(su, negS(s0)))
end

constPS(s::Sum) = PS(isempty(s.t) ? Dict{Ex,Sum}() : Dict{Ex,Sum}(EX0 => s), HUGE_P)

# atan(v) for v with positive valuation
atanSeries(v::PS, P::Q) =
    polyPS(v, k -> iseven(k) ? Q(0) : Q((-1)^((k - 1) ÷ 2)) // k, 0, P)

function atanPS(a::PS, x::Atom, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    if sign(val(a)) < 0
        # a -> ±oo as w -> 0:  atan(a) = σ π/2 - atan(1/a)
        _, c0, _ = split_lead(a)
        σ = sgn(c0, x)
        σ == 0 && throw(GruntzError("could not determine the sign of an atan argument"))
        half_pi = scaleS(atomS(PI_ATOM), Q(σ) // 2)
        return addPS(constPS(half_pi), scalePS(atanSeries(powPS(a, Q(-1), P), P), negS(oneS())))
    end
    # atan(c + u) = atan(c) + atan(u / (1 + c^2 + c u)), valid for every real c
    c0, u = const_and_rest(a)
    den = addPS(constPS(addS(oneS(), mulS(c0, c0))), scalePS(u, c0))
    v = mulPS(u, powPS(den, Q(-1), P))
    addPS(atanSeries(v, P), constPS(mkatan(c0)))
end

# erf(c + u) = erf(c) + 2/sqrt(π) exp(-c^2) sum_{n>=1} (-1)^(n-1) H_{n-1}(c) u^n / n!,
# H_n the Hermite polynomials: H_0 = 1, H_1 = 2c, H_{n+1} = 2c H_n - 2n H_{n-1}.
# The argument is bounded: one that tends to ±oo was rewritten with erfs.
function erfPS(a::PS, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: erf of an unbounded argument"))
    c0, u = const_and_rest(a)
    H = Sum[oneS(), scaleS(c0, Q(2))]
    function coef(n)
        n == 0 && return Q(0)
        while length(H) < n
            j = length(H) - 1
            push!(H, subS(mulS(scaleS(c0, Q(2)), H[end]), scaleS(H[end-1], Q(2j))))
        end
        scaleS(H[n], Q((-1)^(n - 1)) // factorial(big(n)))
    end
    k = scaleS(mulS(mkexp(negS(mulS(c0, c0))), powS(atomS(PI_ATOM), -Q(1) // 2)), Q(2))
    addPS(scalePS(polyPS(u, coef, 1, P), k), constPS(mkerf(c0)))
end

# erfs(v) = exp(v^2) erfc(v), v -> +oo. When v tends to infinity as w -> 0, the
# asymptotic series 1/sqrt(π) sum_{n>=0} (-1)^n (2n-1)!!/2^n v^(-2n-1): its error
# after a term is of the order of the next one, so it is truncated as a convergent
# series would be. Otherwise v = c + u, with c tending to infinity with x but a
# constant for w, and erfs(c + u) = sum_n erfs^(n)(c) u^n / n!: as erfs' = 2t erfs -
# 2/sqrt(π), erfs^(n) = A_n(t) erfs(t) + B_n(t)/sqrt(π) with A_0 = 1, B_0 = 0,
# A_{n+1} = A_n' + 2t A_n, B_{n+1} = B_n' - 2 A_n (polynomials in t).
function erfsPS(a::PS, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    rpi = powS(atomS(PI_ATOM), -Q(1) // 2)
    if sign(val(a)) < 0
        function acoef(k)
            iseven(k) && return Q(0)
            n = (k - 1) ÷ 2
            Q((-1)^n) * prod(Q(2j - 1) // 2 for j in 1:n; init = Q(1))
        end
        return scalePS(polyPS(powPS(a, Q(-1), P), acoef, 1, P), rpi)
    end
    c0, u = const_and_rest(a)
    e0 = mkerfs(c0)
    deriv(p) = Q[(i - 1) * p[i] for i in 2:length(p)]
    times2t(p) = [Q(0); 2 .* p]
    polyadd(p, q) = (n = max(length(p), length(q)); Q[get(p, i, 0) + get(q, i, 0) for i in 1:n])
    peval(p) = foldr((ci, acc) -> addS(constS(ci), mulS(c0, acc)), p; init = zeroS())
    A, B = [Q[1]], [Q[]]
    function tcoef(n)
        while length(A) <= n
            An, Bn = A[end], B[end]
            push!(A, polyadd(deriv(An), times2t(An)))
            push!(B, polyadd(deriv(Bn), -2 .* An))
        end
        scaleS(addS(mulS(peval(A[n+1]), e0), mulS(peval(B[n+1]), rpi)), inv(Q(factorial(big(n)))))
    end
    polyPS(u, tcoef, 0, P)
end

# Bernoulli numbers B_0, B_1, ..., as needed
const BERNOULLI = Q[1]
function bernoulli(n::Int)
    while length(BERNOULLI) <= n
        m = length(BERNOULLI)
        push!(BERNOULLI, -sum(binomial(big(m + 1), j) * BERNOULLI[j+1] for j in 0:m-1) / (m + 1))
    end
    BERNOULLI[n+1]
end

# lgrem(v), the remainder of Stirling's series, for v -> +oo as w -> 0: the asymptotic
# series sum_{k>=1} B_2k / (2k (2k - 1)) v^(1 - 2k), truncated as erfs's is.
function lgremPS(a::PS, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 ||
        throw(GruntzError("gamma: the argument does not tend to infinity in the expansion variable"))
    function coef(j)
        iseven(j) && return Q(0)
        k = (j + 1) ÷ 2
        bernoulli(2k) / (2k * (2k - 1))
    end
    polyPS(powPS(a, Q(-1), P), coef, 1, P)
end

# The auxiliary functions of sinint and cosint, and dawson, for v -> +oo as w -> 0:
#   fsi(v) ~ sum_k (-1)^k (2k)! v^(-2k-1),  gsi(v) ~ sum_k (-1)^k (2k+1)! v^(-2k-2),
#   dawson(v) ~ sum_k (2k-1)!! / 2^(k+1) v^(-2k-1),  eiaux(v) ~ sum_k k! v^(-k-1) (also for
#   v -> -oo),
# asymptotic series truncated as erfs's is.
function auxPS(h::Symbol, a::PS, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 ||
        throw(GruntzError("$h: the argument does not tend to infinity in the expansion variable"))
    function coef(j)
        if h === :gsi
            (j < 2 || isodd(j)) && return Q(0)
            k = (j - 2) ÷ 2
            return Q((-1)^k * factorial(big(2k + 1)))
        end
        h === :eiaux && return j >= 1 ? Q(factorial(big(j - 1))) : Q(0)
        iseven(j) && return Q(0)
        k = (j - 1) ÷ 2
        h === :fsi && return Q((-1)^k * factorial(big(2k)))
        prod(Q(2i - 1) for i in 1:k; init = Q(1)) / Q(2)^(k + 1)
    end
    polyPS(powPS(a, Q(-1), P), coef, 1, P)
end

# sinint, cosint and erfi of a bounded argument c + u, u -> 0, by Taylor's series, with
#   Si' = sin(t)/t, Ci' = cos(t)/t: (sin(t)/t)^(m) = sum_j C(m, j) sin(t + jπ/2) (-1)^(m-j) (m-j)! t^(j-m-1),
#   erfi' = 2/sqrt(π) exp(t^2): (exp(t^2))^(m) = P_m(t) exp(t^2), P_0 = 1, P_(m+1) = P_m' + 2t P_m.
# At c = 0, Si(u) = sum_k (-1)^k u^(2k+1) / ((2k+1) (2k+1)!) and
# Ci(u) = γ + log(u) + sum_(k>=1) (-1)^k u^(2k) / (2k (2k)!). An argument that tends to
# ±oo was rewritten with fsi, gsi or dawson.
const EULER = atomS(leafatom(Base.MathConstants.eulergamma))   # as `from_number` makes it
function specialPS(h::Symbol, a::PS, logw::Sum, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: $h of an unbounded argument"))
    c0, u = const_and_rest(a)
    if h === :erfi
        k = scaleS(mulS(mkexp(mulS(c0, c0)), powS(atomS(PI_ATOM), -Q(1) // 2)), Q(2))
        deriv(p) = Q[(i - 1) * p[i] for i in 2:length(p)]
        polyadd(p, q) = (n = max(length(p), length(q)); Q[get(p, i, 0) + get(q, i, 0) for i in 1:n])
        peval(p) = foldr((ci, acc) -> addS(constS(ci), mulS(c0, acc)), p; init = zeroS())
        Ps = [Q[1]]
        function ecoef(n)
            n == 0 && return Q(0)
            while length(Ps) < n
                push!(Ps, polyadd(deriv(Ps[end]), [Q(0); 2 .* Ps[end]]))
            end
            scaleS(mulS(k, peval(Ps[n])), inv(Q(factorial(big(n)))))
        end
        return addPS(polyPS(u, ecoef, 1, P), constPS(mkodd(:erfi, c0)))
    end
    h === :expinti && return expintiPS(a, c0, u, logw, P)
    if iszero(c0)
        h === :sinint && return polyPS(u, k -> isodd(k) ? Q((-1)^((k - 1) ÷ 2)) // (k * factorial(big(k))) : Q(0), 1, P)
        tail = polyPS(u, k -> iseven(k) ? Q((-1)^(k ÷ 2)) // (k * factorial(big(k))) : Q(0), 2, P)
        return addPS(addPS(tail, logPS(a, logw, P)), constPS(EULER))
    end
    trig = h === :sinint ? mksin : mkcos
    ic = powS(c0, Q(-1))
    function tcoef(n)
        n == 0 && return Q(0)
        m = n - 1
        d = zeroS()
        for j in 0:m
            t = trig(addS(c0, scaleS(atomS(PI_ATOM), Q(j) // 2)))
            d = addS(d, scaleS(mulS(t, powS(ic, Q(m - j + 1))),
                               Q(binomial(big(m), j) * (-1)^(m - j) * factorial(big(m - j)))))
        end
        scaleS(d, inv(Q(factorial(big(n)))))
    end
    c = h === :sinint ? mkodd(:sinint, c0) : mkcosint(c0)
    addPS(polyPS(u, tcoef, 1, P), constPS(c))
end

# Ei(c + u), u -> 0. At c = 0, Ei(u) = γ + log|u| + sum_(k>=1) u^k / (k k!); otherwise by
# Taylor's series with Ei' = exp(t)/t: (exp(t)/t)^(m) = exp(t) sum_j C(m, j) (-1)^j j! t^(-j-1).
function expintiPS(a::PS, c0::Sum, u::PS, logw::Sum, P::Q)
    if iszero(c0)
        _, lc, _ = split_lead(a)
        s = sgn(lc, CONTEXT[].x)                 # log|u|
        tail = polyPS(u, k -> k == 0 ? Q(0) : inv(Q(k * factorial(big(k)))), 1, P)
        return addPS(addPS(tail, logPS(scalePS(a, constS(s)), logw, P)), constPS(EULER))
    end
    ec, ic = mkexp(c0), powS(c0, Q(-1))
    function coef(n)
        n == 0 && return Q(0)
        m = n - 1
        d = zeroS()
        for j in 0:m
            d = addS(d, scaleS(powS(ic, Q(j + 1)), Q(binomial(big(m), j) * (-1)^j * factorial(big(j)))))
        end
        scaleS(mulS(ec, d), inv(Q(factorial(big(n)))))
    end
    addPS(polyPS(u, coef, 1, P), constPS(mkexpinti(c0)))
end

# Cl₂(c + u), u -> 0. At c = 2πk, Cl₂(u) = u - u log|u| + Σ_(n>=1) |B_2n| / (2n (2n+1)!) u^(2n+1);
# otherwise by Taylor's series, with Cl₂' = -log|2 sin(θ/2)| and Cl₂'' = -cot(θ/2)/2,
# d/dθ cot(θ/2) = -(1 + cot²(θ/2))/2. An argument that tends to ±oo oscillates (bounded:
# see `bounded_limit`).
function clausen2PS(a::PS, logw::Sum, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError(OSC_MSG))
    c0, u = const_and_rest(a)
    q = pi_multiple(c0)
    if q !== nothing && isinteger(q) && iseven(numerator(q))
        isempty(u.c) && return PS(Dict{Ex,Sum}(), u.prec)
        _, lc, _ = split_lead(u)
        s = sgn(lc, CONTEXT[].x)                     # log|u|
        poly = polyPS(u, k -> k == 1 ? Q(1) : (isodd(k) ? abs(bernoulli(k - 1)) / ((k - 1) * factorial(big(k))) : Q(0)), 1, P)
        return addPS(poly, scalePS(mulPS(u, logPS(scalePS(u, constS(Q(s))), logw, P)), constS(Q(-1))))
    end
    half = scaleS(c0, Q(1) // 2)
    sn = mksin(half)
    C = mulS(mkcos(half), powS(sn, Q(-1)))          # cot(c/2)
    s2 = scaleS(sn, Q(2))
    σ = try csign(s2) catch err; err isa NeedSign || rethrow(); nothing end
    peval(p) = foldr((ci, acc) -> addS(constS(ci), mulS(C, acc)), p; init = zeroS())
    D = [Q[0, 1]]                                    # d^k/dθ^k cot(θ/2) as a polynomial in C
    function coef(n)
        n == 0 && return Q(0)
        n == 1 && return negS(mklog(σ === nothing ? mkabs(s2) : scaleS(s2, Q(σ))))
        while length(D) < n - 1
            p = D[end]
            dp = Q[(i - 1) * p[i] for i in 2:length(p)]          # p'(C)
            r = zeros(Q, length(dp) + 2)                         # -(1 + C²)/2 p'(C)
            for (i, c) in enumerate(dp)
                r[i] -= c / 2
                r[i+2] -= c / 2
            end
            push!(D, r)
        end
        scaleS(peval(D[n-1]), -inv(Q(2) * factorial(big(n))))
    end
    addPS(polyPS(u, coef, 1, P), constPS(mkclausen2(c0)))
end

# li2(c + u), u -> 0, c < 1. At c = 0, Σ u^k/k²; otherwise by Taylor's series, from
# li2'(c + h) = -log(d - h)/(c + h), d = 1 - c: -log(d - h) = -log(d) + Σ_(k>=1) h^k/(k d^k)
# and 1/(c + h) = Σ_(j>=0) (-h)^j / c^(j+1). An argument that tends to 1 or -oo was
# rewritten (see `resolve_li2`).
function li2PS(a::PS, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: li2 of an unbounded argument"))
    c0, u = const_and_rest(a)
    isempty(c0.t) && return polyPS(u, k -> k == 0 ? Q(0) : inv(Q(k)^2), 1, P)
    ratconst(c0) == 1 && throw(GruntzError("internal error: li2 at its branch point 1"))
    d = subS(oneS(), c0)
    ld, id, ic = mklog(d), powS(d, Q(-1)), powS(c0, Q(-1))
    A(k) = k == 0 ? negS(ld) : scaleS(powS(id, Q(k)), inv(Q(k)))
    B(j) = scaleS(powS(ic, Q(j + 1)), Q(isodd(j) ? -1 : 1))
    G = Sum[]                                        # the Taylor coefficients of li2'
    function coef(n)
        n == 0 && return Q(0)
        while length(G) < n
            m = length(G)
            push!(G, foldl(addS, (mulS(A(k), B(m - k)) for k in 0:m)))
        end
        scaleS(G[n], inv(Q(n)))
    end
    addPS(polyPS(u, coef, 1, P), constPS(mkli2(c0)))
end

# besselk(ν, c + u), u -> 0, c > 0, by Taylor's series:
#   K_ν^(n) = (-1/2)^n sum_j C(n, j) K_(ν-n+2j),  K_(-μ) = K_μ
function besselkPS(a::PS, ν::Sum, logw::Sum, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: besselk of an unbounded argument"))
    sign(val(a)) > 0 && return besselk0PS(a, ratconst(ν)::Q, logw, P)
    c0, u = const_and_rest(a)
    nu = ratconst(ν)::Q
    function coef(n)
        n == 0 && return Q(0)
        d = zeroS()
        for j in 0:n
            d = addS(d, scaleS(mkbesselk(constS(nu - n + 2j), c0), Q(binomial(big(n), j))))
        end
        scaleS(d, (-Q(1) // 2)^n / factorial(big(n)))
    end
    addPS(polyPS(u, coef, 1, P), constPS(mkbesselk(ν, c0)))
end

# besseli(ν, c + u), u -> 0, by Taylor's series, I_ν^(n) = (1/2)^n sum_j C(n, j) I_(ν-n+2j);
# at c = 0, I_ν(z) = (z/2)^ν sum_k t^k / (k! Γ(ν + k + 1)), t = z^2/4
function besseliPS(a::PS, ν::Sum, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: besseli of an unbounded argument"))
    nu = ratconst(ν)::Q
    if sign(val(a)) > 0
        nu < 0 && isinteger(nu) && (nu = -nu)
        half = scalePS(a, constS(Q(1) // 2))
        t = scalePS(mulPS(a, a), constS(Q(1) // 4))
        ired = polyPS(t, k -> inv(Q(factorial(big(k))) * prod((nu + j for j in 1:k); init = Q(1))), 0, P)
        return scalePS(mulPS(powPS(half, nu, P), ired), powS(mkgamma(constS(nu + 1)), Q(-1)))
    end
    c0, u = const_and_rest(a)
    function coef(n)
        n == 0 && return Q(0)
        d = zeroS()
        for j in 0:n
            d = addS(d, scaleS(mkbesseli(constS(nu - n + 2j), c0), Q(binomial(big(n), j))))
        end
        scaleS(d, (Q(1) // 2)^n / factorial(big(n)))
    end
    addPS(polyPS(u, coef, 1, P), constPS(mkbesseli(ν, c0)))
end

# jred(z, ν) = J_ν(z) (z/2)^(-ν) = sum_k (-1)^k t^k / (k! Γ(ν + k + 1)), t = z^2/4
function jredPS(a::PS, ν::Sum, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: besselj of an unbounded argument"))
    t = scalePS(mulPS(a, a), constS(Q(1) // 4))
    function coef(k)
        d = constS(Q(factorial(big(k))))
        for j in 1:k
            d = mulS(d, addS(ν, constS(Q(j))))
        end
        scaleS(powS(d, Q(-1)), Q(isodd(k) ? -1 : 1))
    end
    scalePS(polyPS(t, coef, 0, P), powS(mkgamma(addS(ν, oneS())), Q(-1)))
end

# besselj(ν, c + u), c != 0, u -> 0, by Taylor's series:
# J_ν^(n)(c) = 2^(-n) sum_j (-1)^j binomial(n, j) J_(ν-n+2j)(c)
function besseljPS(a::PS, ν::Sum, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: besselj of an unbounded argument"))
    sign(val(a)) > 0 && throw(GruntzError("internal error: besselj at 0 (see `resolve_besselj`)"))
    c0, u = const_and_rest(a)
    function coef(n)
        n == 0 && return Q(0)
        d = zeroS()
        for j in 0:n
            d = addS(d, scaleS(mkbesselj(addS(ν, constS(Q(2j - n))), c0), Q((-1)^j * binomial(big(n), j))))
        end
        scaleS(d, (Q(1) // 2)^n / factorial(big(n)))
    end
    addPS(polyPS(u, coef, 1, P), constPS(mkbesselj(ν, c0)))
end

# besselk(ν, z), z -> 0+ (positive valuation), with t = z^2/4 (DLMF 10.25.2, 10.27.4, 10.31.1):
#   I_μ(z) = (z/2)^μ sum_k t^k / (k! Γ(μ + k + 1)),
#   K_ν = π/(2 sin(νπ)) (I_(-ν) - I_ν) for ν not an integer, and for an integer n >= 0
#   K_n(z) = 1/2 (z/2)^(-n) sum_(k<n) (n-k-1)!/k! (-t)^k + (-1)^(n+1) log(z/2) I_n(z)
#            + (-1)^n 1/2 (z/2)^n sum_k (ψ(k+1) + ψ(n+k+1)) t^k / (k! (n+k)!),
#   ψ(m+1) = -γ + H_m.
function besselk0PS(z::PS, nu::Q, logw::Sum, P::Q)
    half = scalePS(z, constS(Q(1) // 2))
    t = scalePS(mulPS(z, z), constS(Q(1) // 4))
    # I_μ(z) (z/2)^(-μ) Γ(μ + 1): coefficients 1/(k! (μ+1)_k)
    function Ired(μ::Q)
        polyPS(t, k -> inv(Q(factorial(big(k))) * prod((μ + j for j in 1:k); init = Q(1))), 0, P)
    end
    if !isinteger(nu)
        I(μ) = scalePS(mulPS(powPS(half, μ, P), Ired(μ)), powS(mkgamma(constS(μ + 1)), Q(-1)))
        k = mulS(scaleS(atomS(PI_ATOM), Q(1) // 2), powS(mksin(scaleS(atomS(PI_ATOM), nu)), Q(-1)))
        return scalePS(addPS(I(-nu), scalePS(I(nu), negS(oneS()))), k)
    end
    n = Int(abs(nu))
    sg = iseven(n) ? 1 : -1
    hpos = n == 0 ? onePS() : powPS(half, Q(n), P)
    In = scalePS(mulPS(hpos, Ired(Q(n))), constS(inv(Q(factorial(big(n))))))
    acc = scalePS(mulPS(logPS(half, logw, P), In), constS(Q(-sg)))
    H(m) = sum((Q(1) // j for j in 1:m); init = Q(0))
    coef(k) = scaleS(addS(scaleS(EULER, Q(-2)), constS(H(k) + H(n + k))),
                     inv(Q(factorial(big(k)) * factorial(big(n + k)))))
    acc = addPS(acc, scalePS(mulPS(hpos, polyPS(t, coef, 0, P)), constS(Q(sg) // 2)))
    if n > 0
        A = polyPS(t, k -> k < n ? Q((-1)^k * factorial(big(n - k - 1))) // factorial(big(k)) : Q(0), 0, P)
        acc = addPS(acc, scalePS(mulPS(powPS(half, Q(-n), P), A), constS(Q(1) // 2)))
    end
    acc
end

# gamma(c + v), v -> 0: log Γ(c + v) = log Γ(c) + sum_(k>=1) ψ^(k-1)(c) v^k / k!, and at a
# pole c = -n, Γ(v - n) = Γ(1 + v) / (v (v - 1) ... (v - n))
function gammaPS(a::PS, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: gamma of an unbounded argument"))
    c0, v = const_and_rest(a)
    r = ratconst(c0)
    taylor(c) = scalePS(expPS(polyPS(v, k -> k == 0 ? Q(0) : scaleS(mkpolygamma(k - 1, c), inv(Q(factorial(big(k))))), 1, P), P),
                        mkgamma(c))
    (r === nothing || !isinteger(r) || r > 0) && return taylor(c0)
    den = onePS()
    for j in 0:Int(-r)
        den = mulPS(den, addPS(v, constPS(constS(Q(-j)))))
    end
    mulPS(taylor(oneS()), powPS(den, Q(-1), P))
end

# ψ^(k)(c + v), v -> 0: sum_j ψ^(k+j)(c) v^j / j!, and at a pole c = -n, by
# ψ^(k)(z) = ψ^(k)(z + n + 1) - (-1)^k k! sum_(j=0..n) (z + j)^(-k-1)
function polygammaPS(a::PS, k::Int, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: polygamma of an unbounded argument"))
    c0, v = const_and_rest(a)
    r = ratconst(c0)
    taylor(c) = polyPS(v, j -> scaleS(mkpolygamma(k + j, c), inv(Q(factorial(big(j))))), 0, P)
    (r === nothing || !isinteger(r) || r > 0) && return taylor(c0)
    acc = taylor(oneS())
    kf = Q((-1)^(k + 1) * factorial(big(k)))
    for j in 0:Int(-r)
        acc = addPS(acc, scalePS(powPS(addPS(v, constPS(constS(Q(j) + r))), Q(-k - 1), P), constS(kf)))
    end
    acc
end

# psiaux(v, k) for v -> +oo, t = 1/v (asymptotic, truncated as erfs's is):
#   k = 0: ψ(v) - log(v) ~ -t/2 - sum_(j>=1) B_2j/(2j) t^(2j),
#   k >= 1: ψ^(k)(v) ~ (-1)^(k+1) ((k-1)! t^k + k!/2 t^(k+1) + sum_(j>=1) B_2j (2j+k-1)!/(2j)! t^(2j+k))
function psiauxPS(a::PS, k::Int, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 ||
        throw(GruntzError("polygamma: the argument does not tend to infinity in the expansion variable"))
    function coef(i)
        if k == 0
            i == 1 && return Q(-1) // 2
            return iseven(i) ? -bernoulli(i) / i : Q(0)
        end
        s = Q((-1)^(k + 1))
        i < k && return Q(0)
        i == k && return s * factorial(big(k - 1))
        i == k + 1 && return s * factorial(big(k)) / 2
        m = i - k
        isodd(m) && return Q(0)
        s * bernoulli(m) * Q(factorial(big(i - 1))) / factorial(big(m))
    end
    polyPS(powPS(a, Q(-1), P), coef, 1, P)
end

# kaux_ν(v) ~ sum_k a_k(ν) v^(-k), a_k = prod_(j=1..k) (4ν^2 - (2j-1)^2) / (k! 8^k), for
# v -> +oo (Hankel's expansion); a finite series for a half-integer ν
# iaux_ν(v) ~ sum_k (-1)^k a_k(ν) v^(-k), for besseli (`alt`)
function kauxPS(a::PS, ν::Sum, P::Q; alt::Bool = false)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 ||
        throw(GruntzError("kaux: the argument does not tend to infinity in the expansion variable"))
    nu = ratconst(ν)::Q
    coef(k) = Q(alt && isodd(k) ? -1 : 1) *
              prod((4nu^2 - Q(2j - 1)^2 for j in 1:k); init = Q(1)) / (factorial(big(k)) * Q(8)^k)
    polyPS(powPS(a, Q(-1), P), coef, 0, P)
end

# lambertw(c + u), u -> 0. At c = 0, W(u) = sum_(n>=1) (-n)^(n-1) u^n / n!. Otherwise by
# Taylor's series, from z (1 + W) W' = W: with W(c + h) = sum_n a_n h^n and
# b_n = sum_(k=0..n) (δ_k0 + a_k) (n - k + 1) a_(n-k+1), c b_n + b_(n-1) = a_n. An
# argument that tends to +oo was rewritten with wexp.
function lambertwPS(a::PS, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    sign(val(a)) < 0 && throw(GruntzError("internal error: lambertw of an unbounded argument"))
    c0, u = const_and_rest(a)
    isempty(c0.t) && return polyPS(u, n -> n == 0 ? Q(0) : Q(big(-n)^(n - 1)) // factorial(big(n)), 1, P)
    W0 = mklambertw(c0)
    ic, iw = powS(c0, Q(-1)), powS(addS(oneS(), W0), Q(-1))
    A, B = Sum[W0], Sum[]
    function coef(n)
        while length(A) <= n
            m = length(A) - 1                # a_0..a_m known: b_m, then a_(m+1)
            push!(B, mulS(subS(A[m+1], m == 0 ? zeroS() : B[m]), ic))
            s = B[m+1]
            for k in 1:m
                s = subS(s, scaleS(mulS(A[k+1], A[m-k+2]), Q(m - k + 1)))
            end
            push!(A, scaleS(mulS(s, iw), inv(Q(m + 1))))
        end
        A[n+1]
    end
    addPS(polyPS(u, coef, 1, P), constPS(W0))
end

# wexp(L) = W(exp(L)), the solution F of F + log(F) = L. For L tending to infinity as
# w -> 0, the asymptotic series (de Bruijn; Corless et al. 1996)
#   F = L - l + sum_(k>=1) L^(-k) sum_(m=1..k) c_(k-m,m) l^m,  l = log(L),
#   c_(j,m) = (-1)^j [j+m, j+1] / m!  ([n, k] the unsigned Stirling numbers of the first kind),
# its terms of order k a power w^(k v) (times powers of log(w)), truncated as a convergent
# series would be. Otherwise L = c + u, c a constant for w, and F(c + u) by Taylor's
# series, from (1 + F) F' = F: (1 + a_0) (n + 1) a_(n+1) = a_n - sum_(k=1..n) a_k (n - k + 1) a_(n-k+1).
const STIRLING1 = Dict{Tuple{Int,Int},BigInt}()
function stirling1(n::Int, k::Int)
    (n == k) && return big(1)
    (k == 0 || k > n) && return big(0)
    get!(STIRLING1, (n, k)) do
        (n - 1) * stirling1(n - 1, k) + stirling1(n - 1, k - 1)
    end
end
function wexpPS(a::PS, logw::Sum, P::Q)
    isempty(a.c) && throw(NeedMorePrecision())
    if sign(val(a)) < 0
        Li = powPS(a, Q(-1), P)
        l = logPS(a, logw, P)
        v = val(Li)
        K = israt(v) ? Int(ceil(BigInt, P / v.q)) : 4
        acc = addPS(a, scalePS(l, negS(oneS())))
        israt(v) || (acc = PS(acc.c, pmin(acc.prec, Prec(v * Q(K + 1)))))
        acc = PS(acc.c, pmin(acc.prec, Prec(Ex(P))))
        Lk = onePS()
        for k in 1:K
            Lk = mulPS(Lk, Li)
            poly = PS(Dict{Ex,Sum}(), HUGE_P)       # sum_m c_(k-m,m) l^m
            lm = onePS()
            for m in 1:k
                lm = mulPS(lm, l)
                c = Q((-1)^(k - m) * stirling1(k, k - m + 1)) // factorial(big(m))
                poly = addPS(poly, scalePS(lm, constS(c)))
            end
            acc = addPS(acc, mulPS(Lk, poly))
        end
        return acc
    end
    c0, u = const_and_rest(a)
    F0 = mkwexp(c0)
    iw = powS(addS(oneS(), F0), Q(-1))
    A = Sum[F0]
    function coef(n)
        while length(A) <= n
            m = length(A) - 1
            s = A[m+1]
            for k in 1:m
                s = subS(s, scaleS(mulS(A[k+1], A[m-k+2]), Q(m - k + 1)))
            end
            push!(A, scaleS(mulS(s, iw), inv(Q(m + 1))))
        end
        A[n+1]
    end
    addPS(polyPS(u, coef, 1, P), constPS(F0))
end

function logPS(a::PS, logw::Sum, P::Q)
    v, c0, r = split_lead(a)
    L = polyPS(r, k -> Q((-1)^(k + 1)) // k, 1, P)
    cst = addS(mklog(c0), mulS(logw, toS(v)))
    addPS(L, constPS(cst))
end

function series_atom(a::Atom, w::Atom, logw::Sum, P::Q, x::Atom)
    a.kind === :leaf && return PS(Dict{Ex,Sum}((a == w ? EX1 : Ex(Q(0), a.head::Sum)) => oneS()), HUGE_P)
    a.kind === :base && return series(a.args[1]::Sum, w, logw, P, x)
    arg = series(a.args[1]::Sum, w, logw, P, x)
    h = a.head
    h === :exp ? expPS(arg, P) :
    h === :log ? logPS(arg, logw, P) :
    h === :atan ? atanPS(arg, x, P) :
    h === :erf ? erfPS(arg, P) :
    h === :erfs ? erfsPS(arg, P) :
    h === :lgrem ? lgremPS(arg, P) :
    h === :lambertw ? lambertwPS(arg, P) :
    h === :gamma ? gammaPS(arg, P) :
    h === :polygamma ? polygammaPS(arg, Int(ratconst(a.args[2]::Sum)::Q), P) :
    h === :psiaux ? psiauxPS(arg, Int(ratconst(a.args[2]::Sum)::Q), P) :
    h === :wexp ? wexpPS(arg, logw, P) :
    h in (:fsi, :gsi, :dawson, :eiaux) ? auxPS(h, arg, P) :
    h in (:sinint, :cosint, :erfi, :expinti) ? specialPS(h, arg, logw, P) :
    h === :clausen2 ? clausen2PS(arg, logw, P) :
    h === :li2 ? li2PS(arg, P) :
    h === :besselk ? besselkPS(arg, a.args[2]::Sum, logw, P) :
    h === :kaux ? kauxPS(arg, a.args[2]::Sum, P) :
    h === :besseli ? besseliPS(arg, a.args[2]::Sum, P) :
    h === :besselj ? besseljPS(arg, a.args[2]::Sum, P) :
    h === :jred ? jredPS(arg, a.args[2]::Sum, P) :
    h === :iaux ? kauxPS(arg, a.args[2]::Sum, P; alt = true) :
    h === :fracpart ? throw(GruntzError(OSC_MSG)) :        # bounded, decided by `bounded_limit`
    h === :sin ? trigPS(arg, P)[1] :
    h === :cos ? trigPS(arg, P)[2] :
    h in (:abs, :sign) ? signPS(h, arg, x) :
    throw(GruntzError("no series for `$h`"))
end

# abs(u) = σ u and sign(u) = σ, σ the eventual sign of u's leading coefficient. An
# oscillating one (abs(cos(x) exp(-x))) stops the algorithm (see `bounded_limit`).
function signPS(h::Symbol, a::PS, x::Atom)
    _, c0, _ = split_lead(a)
    σ = Q(sgn(c0, x))
    h === :abs ? scalePS(a, constS(σ)) : constPS(constS(σ))
end

function series(s::Sum, w::Atom, logw::Sum, P::Q, x::Atom)::PS
    acc = PS(Dict{Ex,Sum}(), HUGE_P)     # inexact terms carry their own precision
    for (m, c) in s.t
        cst = constS(c)
        ps = nothing
        for (a, e) in m.fs
            if hasw(a)
                pe = powPS(series_atom(a, w, logw, P, x), e, P)
                ps = ps === nothing ? pe : mulPS(ps, pe)
            else
                cst = mulS(cst, powS(atomS(a), e))
            end
        end
        term = ps === nothing ?
               constPS(cst) :
               scalePS(ps, cst)
        acc = addPS(acc, term)
    end
    acc
end

# A coefficient free of x whose value is zero (to the precision `csign` uses) is
# a zero the simplifier did not recognise; taking it as the leading coefficient
# would give a wrong limit. When splitting into cases, coefficients with parameters
# are tested too (see `zerostate`); one with x is zero when the constant
# coefficient of each of its x-parts is.
function numzero(s::Sum, x::Atom)
    if !hasleaf(s, x.key)
        z = zerostate(s)
        z isa NeedSign && throw(z)
        return z
    end
    CONTEXT[].cases || return false
    groups = Dict{String,Sum}()
    for (m, c) in s.t
        k = Mono(filter(p -> hasleaf(p.first, x.key), m.fs)).key
        groups[k] = addS(get(groups, k, zeroS()), monoS(Mono(filter(p -> !hasleaf(p.first, x.key), m.fs)), c))
    end
    zs = [zerostate(g) for g in values(groups)]
    any(z -> z === false, zs) && return false
    i = findfirst(z -> z isa NeedSign, zs)
    i === nothing || throw(zs[i])
    true
end

# When splitting into cases, leading coefficients that may vanish (b in b/w^2 + 1)
# are tested, and dropped when zero
function dropzeros(a::PS)
    if !CONTEXT[].cases
        # outside cases only a leading p - |p| is tested (see `zerostate`)
        isempty(a.c) || numzero(a.c[val(a)], CONTEXT[].x)
        return a
    end
    ks = sort!(collect(keys(a.c)))
    i = findfirst(k -> !numzero(a.c[k], CONTEXT[].x), ks)
    i === nothing && return PS(Dict{Ex,Sum}(), a.prec)
    i == 1 ? a : PS(Dict{Ex,Sum}(k => a.c[k] for k in ks[i:end]), a.prec)
end

# The precision of the series is doubled from 4 up to LEADTERM_MAXP. The limits in the
# tests and benchmarks need at most 16; the cost grows about tenfold with each doubling
# (an unrecognised zero, whose terms cancel to every order, takes 0.2 s at 64 but 20 s
# at 256), so going further only delays the error.
const LEADTERM_MAXP = Q(64)

function leadterm(f::Sum, w::Atom, logw::Sum, x::Atom; maxP::Q = LEADTERM_MAXP)
    P = Q(4)
    while P <= maxP
        try
            ps = series(f, w, logw, P, x)
            ks = sort!(collect(keys(ps.c)))
            i = findfirst(k -> !numzero(ps.c[k], x), ks)
            i === nothing || return ps.c[ks[i]], ks[i]
            # an exact series with only zero coefficients: f is 0, as under a condition
            # c = 0 not solved for a parameter (see `solve_cases`), (a^3 + a + 1) x
            CONTEXT[].cases && isexact(ps.prec) && return zeroS(), EX0
        catch err
            err isa NeedMorePrecision || rethrow()
        end
        P *= 2
    end
    throw(GruntzError("could not determine the leading term (deep cancellation, " *
                      "or a zero that the internal simplifier cannot recognise)"))
end
