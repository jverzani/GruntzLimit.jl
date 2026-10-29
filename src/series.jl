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

# sum_{k>=kmin} coef(k) u^k, u having positive valuation; relative target `Trel`.
# A coefficient is a rational or a constant `Sum`.
# A valuation with a parameter (w^a) has no numerical value: a few terms are taken
# and the precision is that of the first one left out.
function polyPS(u::PS, coef, kmin::Int, Trel::Q)
    acc = PS(Dict{Ex,Sum}(), pmin(Prec(Ex(Trel)), u.prec))
    v = isempty(u.c) ? EX0 : val(u)
    K = if isempty(u.c)
        kmin
    elseif israt(v)
        max(kmin, Int(ceil(BigInt, Trel / v.q)))
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

function const_and_rest(a::PS)
    all(b -> EX0 < b, a.prec.bs) || throw(NeedMorePrecision())
    any(k -> k < EX0, keys(a.c)) &&
        throw(GruntzError("argument of exp/sin/cos diverges (oscillation or essential singularity)"))
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
    h === :sin ? trigPS(arg, P)[1] : trigPS(arg, P)[2]
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
    CONTEXT[].cases || return a
    ks = sort!(collect(keys(a.c)))
    i = findfirst(k -> !numzero(a.c[k], CONTEXT[].x), ks)
    i === nothing && return PS(Dict{Ex,Sum}(), a.prec)
    i == 1 ? a : PS(Dict{Ex,Sum}(k => a.c[k] for k in ks[i:end]), a.prec)
end

function leadterm(f::Sum, w::Atom, logw::Sum, x::Atom)
    P = Q(4)
    for _ in 1:8
        try
            ps = series(f, w, logw, P, x)
            ks = sort!(collect(keys(ps.c)))
            i = findfirst(k -> !numzero(ps.c[k], x), ks)
            i === nothing || return ps.c[ks[i]], ks[i]
        catch err
            err isa NeedMorePrecision || rethrow()
        end
        P *= 2
    end
    throw(GruntzError("could not determine the leading term (deep cancellation, " *
                      "or a zero that the internal simplifier cannot recognise)"))
end
