# ---------------------------------------------------------------------------
# Canonical form
# ---------------------------------------------------------------------------
struct Atom
    kind::Symbol          # :leaf, :fun (exp/log/sin/cos), :base (multi-term sum used as base)
    head::Any
    args::Vector{Any}     # Vector of Sum
    key::String
end
Base.:(==)(a::Atom, b::Atom) = a.key == b.key
Base.hash(a::Atom, h::UInt) = hash(a.key, h)

struct Mono
    fs::Vector{Pair{Atom,Q}}   # sorted by atom key, exponents nonzero
    key::String
end
Mono(fs::Vector{Pair{Atom,Q}}) = Mono(fs, join(("$(a.key)^$(e)" for (a, e) in fs), "*"))
Base.:(==)(a::Mono, b::Mono) = a.key == b.key
Base.hash(a::Mono, h::UInt) = hash(a.key, h)

struct Sum
    t::Dict{Mono,Q}
end
Base.iszero(s::Sum) = isempty(s.t)

const ONEMONO = Mono(Pair{Atom,Q}[])
zeroS() = Sum(Dict{Mono,Q}())
constS(c) = iszero(c) ? zeroS() : Sum(Dict{Mono,Q}(ONEMONO => Q(c)))
oneS() = constS(1)
monoS(m::Mono, c::Q) = Sum(Dict{Mono,Q}(m => c))
atomS(a::Atom) = monoS(Mono(Pair{Atom,Q}[a => Q(1)]), Q(1))

skey(s::Sum) = isempty(s.t) ? "0" : join(sort!(String["$(c)*$(m.key)" for (m, c) in s.t]), "+")

leafatom(obj) = Atom(:leaf, obj, Any[], "L:" * string(obj))
funatom(h::Symbol, args::Vector{Sum}) =
    Atom(:fun, h, Any[args...], string(h, "(", join([skey(a) for a in args], ","), ")"))
baseatom(s::Sum) = Atom(:base, nothing, Any[s], "B(" * skey(s) * ")")

const WLEAF = leafatom(:__gruntz_w__)

mono(d::Dict{Atom,Q}) = Mono(sort!(collect(d); by = p -> p.first.key))

function mulMono(a::Mono, b::Mono)
    d = Dict{Atom,Q}(a.fs)
    for (at, e) in b.fs
        v = get(d, at, zero(Q)) + e
        iszero(v) ? delete!(d, at) : (d[at] = v)
    end
    mono(d)
end
powMono(m::Mono, q::Q) = Mono(Pair{Atom,Q}[a => e * q for (a, e) in m.fs])

function addS(a::Sum, b::Sum)
    d = copy(a.t)
    for (m, c) in b.t
        v = get(d, m, zero(Q)) + c
        iszero(v) ? delete!(d, m) : (d[m] = v)
    end
    Sum(d)
end
scaleS(a::Sum, c::Q) = iszero(c) ? zeroS() : Sum(Dict{Mono,Q}(m => c * v for (m, v) in a.t))
negS(a::Sum) = scaleS(a, Q(-1))
subS(a::Sum, b::Sum) = addS(a, negS(b))
# Normalises the base atoms of a monomial; returns the coefficient and the monomial.
# * A rational base has an exponent in (0, 1): 2^(-1/2) = 2^(1/2) / 2.
# * A factor M^k, k an integer, next to the base (-M)^r (from a fractional power of -M,
#   as in a/sqrt(-a)) is joined to it: M^k (-M)^r = (-1)^k (-M)^(k+r).
# Otherwise 1/sqrt(2) - sqrt(2)/2 or a/sqrt(-a) + sqrt(-a), which are 0, are not
# recognised as zero.
function normbases(m::Mono)
    any(p -> p.first.kind === :base, m.fs) || return Q(1), m
    d, k0 = Dict{Atom,Q}(m.fs), Q(1)
    for (b, r) in m.fs
        b.kind === :base || continue
        s = b.args[1]::Sum
        length(s.t) == 1 || continue
        mm, c = first(s.t)
        if isempty(mm.fs)
            n = floor(r)
            iszero(n) && continue
            k0 *= c^Int(n)
            r -= n
        elseif c == -1 && all(p -> isone(denominator(p.second)), mm.fs)
            a1, e1 = mm.fs[1]
            k = get(d, a1, zero(Q)) / e1
            (iszero(k) || !isone(denominator(k)) || any(p -> get(d, p.first, zero(Q)) != k * p.second, mm.fs)) &&
                continue
            foreach(p -> delete!(d, p.first), mm.fs)
            r += k
            isodd(numerator(k)) && (k0 = -k0)
        else
            continue
        end
        iszero(r) ? delete!(d, b) : (d[b] = r)
    end
    k0, mono(d)
end

function mulS(a::Sum, b::Sum)
    d = Dict{Mono,Q}()
    for (m1, c1) in a.t, (m2, c2) in b.t
        k, m = normbases(mulMono(m1, m2))
        v = get(d, m, zero(Q)) + k * c1 * c2
        iszero(v) ? delete!(d, m) : (d[m] = v)
    end
    Sum(d)
end

function ratconst(s::Sum)
    isempty(s.t) && return Q(0)
    length(s.t) == 1 || return nothing
    m, c = first(s.t)
    isempty(m.fs) ? c : nothing
end

hasleaf(a::Atom, k::String) =
    a.kind === :leaf ? a.key == k : any(u -> hasleaf(u::Sum, k), a.args)
hasleaf(s::Sum, k::String) = any(m -> any(p -> hasleaf(p.first, k), m.fs), keys(s.t))
hasatom(a::Atom, k::String) = a.key == k || any(u -> hasatom(u::Sum, k), a.args)
hasatom(s::Sum, k::String) = any(m -> any(p -> hasatom(p.first, k), m.fs), keys(s.t))

# --- deferred domain checks -------------------------------------------------
# While the input is converted (`limit_value`), the limit variable x is just a
# symbol, but `_limit` then replaces it by x0 + 1/x, x0 - 1/x or -x. So a monomial in
# x with a negative coefficient, as in log(-x) or sqrt(-x), may be positive where the
# limit is taken, and the sign of a parameter in it (log(a*x), a < 0) can only be
# required after the substitution. During conversion logs and fractional powers of
# monomials in x are kept unevaluated;
# `_limit` rebuilds the expression after its substitution (with the deferral off),
# which simplifies them or raises the domain error then.
const DEFER_DOMAIN = ScopedValue(false)
# a real expression retried on the principal branches of log and fractional powers of
# arguments in x (see `limit_value`)
const BRANCH_X = ScopedValue(false)
_defer_domain(m::Mono) = DEFER_DOMAIN[] && any(p -> hasleaf(p.first, CONTEXT[].x.key), m.fs)

# --- rational powers --------------------------------------------------------
function iroot(n::BigInt, k::Int)
    n == 0 && return big(0)
    r = round(BigInt, BigFloat(n)^inv(BigFloat(k)))
    r^k == n ? r : nothing
end

function ratpow(c::Q, e::Q)
    if isone(denominator(e))
        n = numerator(e)
        abs(n) > 100_000 && throw(GruntzError("exponent too large"))
        return c^Int(n)
    end
    c < 0 && throw(GruntzError("complex power of a negative number", :undefined))
    p, d = Int(numerator(e)), Int(denominator(e))
    rn = iroot(numerator(c), d)
    rd = iroot(denominator(c), d)
    (rn === nothing || rd === nothing) && return nothing
    (rn // rd)^p
end

# (a^e)^q for a fractional q is a^(e q) only for a > 0; for an even e it is |a|^(e q),
# which is (-a)^(e q) where a < 0 (sqrt(log(x)^2) = -log(x) for x < 1). Factors of x
# are decided here, by their sign as x -> +oo: monomials in x are kept unevaluated while
# the input is converted (see DEFER_DOMAIN) and built after `_limit`'s substitution, so
# x is then the variable that tends to +oo. When that sign cannot be decided the factor
# becomes abs(a), resolved later (see `resolve_piecewise`).
function evenpow_signs(m::Mono, q::Q)
    any(p -> _maybe_negative(p...), m.fs) || return Q(1), powMono(m, q)
    k, mm = Q(1), ONEMONO
    for (a, e) in m.fs
        eq = e * q
        b = a
        if _maybe_negative(a, e)
            σ = varsign(a)
            if σ == 0
                b = funatom(:abs, Sum[atomS(a)])
            elseif σ < 0
                if isone(denominator(eq))
                    isodd(numerator(eq)) && (k = -k)       # (-a)^n = (-1)^n a^n
                else
                    b = baseatom(negatom(a))
                end
            end
        end
        mm = mulMono(mm, Mono(Pair{Atom,Q}[b => eq]))
    end
    k, mm
end
# an even power of an atom of x that may be negative
_maybe_negative(a::Atom, e::Q) = isone(denominator(e)) && iseven(numerator(e)) && signable(a)
# an atom of x (not of the expansion variable w) that may be negative: not x, exp or abs
signable(a::Atom) = a.kind !== :leaf && !(a.kind === :fun && a.head in (:exp, :abs)) &&
    hasleaf(a, CONTEXT[].x.key) && !hasw(a)
# the eventual sign of such an atom as x -> +oo; 0 when it cannot be decided
function varsign(a::Atom)
    try
        sgn(atomS(a), CONTEXT[].x)
    catch err
        err isa Union{GruntzError,NeedMorePrecision} || rethrow()
        0
    end
end

# c^q = (c^(1/k))^(k q) for the largest k dividing q's denominator with c a perfect
# k-th power: 4^(1/4) = 2^(1/2)
function rootreduce(c::Q, q::Q)
    d = Int(denominator(q))
    for k in d-1:-1:2
        d % k == 0 || continue
        rn, rd = iroot(numerator(c), k), iroot(denominator(c), k)
        (rn === nothing || rd === nothing) || return rn // rd, q * k
    end
    c, q
end

function powS(s::Sum, q::Q)
    iszero(q) && return oneS()
    if isempty(s.t)
        q > 0 && return zeroS()
        throw(GruntzError("division by zero", :undefined))
    end
    if length(s.t) == 1
        m, c = first(s.t)
        if !isone(denominator(q))
            _defer_domain(m) && return monoS(Mono(Pair{Atom,Q}[baseatom(s) => q]), Q(1))   # checked later
            require_positive(s; strict = q < 0, what = "fractional power")
        end
        if !isone(denominator(q)) && needs_signs(m, c)
            pf = positive_factors(m, c)
            # in the expansion variable w the sign is checked by the series
            pf === nothing && any(p -> hasw(p.first), m.fs) &&
                return monoS(Mono(Pair{Atom,Q}[baseatom(s) => q]), Q(1))
            if pf !== nothing                    # otherwise ratpow raises the error
                c2, kept, negs, grp = pf
                mm = powMono(kept, q)            # (a^e)^q = ((-a)^e)^q, for a < 0
                k = Q(1)
                for (a, e) in negs
                    eq = e * q
                    if isone(denominator(eq))    # (-a)^n = (-1)^n a^n
                        isodd(numerator(eq)) && (k = -k)
                        mm = mulMono(mm, Mono(Pair{Atom,Q}[a => eq]))
                    else
                        mm = mulMono(mm, Mono(Pair{Atom,Q}[baseatom(negatom(a)) => eq]))
                    end
                end
                grp === nothing || (mm = mulMono(mm, Mono(Pair{Atom,Q}[baseatom(grp) => q])))
                return mulS(powS(constS(c2), q), monoS(mm, k))
            end
        end
        k, mm = isone(denominator(q)) ? (Q(1), powMono(m, q)) : evenpow_signs(m, q)
        r = ratpow(c, q)
        if r === nothing
            c, q = rootreduce(c, q)
            mm = mulMono(mm, Mono(Pair{Atom,Q}[baseatom(constS(c)) => q]))
            r = Q(1)
        end
        return monoS(mm, k * r)
    end
    # 1/c for a constant c that is 0 in the context (a case c = 0 not solved for a
    # parameter, see `solve_cases`)
    q < 0 && CONTEXT[].cases && !any(m -> any(p -> hasvar(p.first), m.fs), keys(s.t)) &&
        possible_signs(s) == [0] &&
        throw(GruntzError("division by zero", :undefined))
    if isone(denominator(q)) && 0 < q <= 8
        res = s
        for _ in 2:Int(q)
            res = mulS(res, s)
        end
        return res
    end
    if denominator(q) == 2 && !hasleaf(s, CONTEXT[].x.key) && !hasatom(s, WLEAF.key)
        r = sqrt_poly(s)
        r === nothing || return square_pow(r..., q)
    end
    !isone(denominator(q)) && require_positive(s; strict = q < 0, what = "fractional power")
    monoS(Mono(Pair{Atom,Q}[baseatom(s) => q]), Q(1))
end

# A constant c p^2, c > 0 and p a polynomial (in parameters and atoms) with leading
# coefficient 1: (c p^2)^q = c^q |p|^(2q) for q = n/2, |p| = ±p when the context decides the
# sign of p, so that m + 1 - sqrt(m^2 + 2m + 1) is 0 for m > -1. Otherwise it is abs(p),
# or, when splitting into cases, the cases are on the sign of p.
function square_pow(c::Q, p::Sum, q::Q)
    σ = try
        csign(p)
    catch err
        (err isa NeedSign && !CONTEXT[].cases) || rethrow()
        nothing
    end
    a = σ === nothing ? mkabs(p) : scaleS(p, Q(σ))
    mulS(powS(constS(c), q), powS(a, 2q))
end

# graded lexicographic order on monomials (atoms by key)
function mono_lt(a::Mono, b::Mono)
    da, db = sum(last, a.fs; init = Q(0)), sum(last, b.fs; init = Q(0))
    da == db || return da < db
    for (pa, pb) in zip(a.fs, b.fs)
        pa.first.key == pb.first.key || return pa.first.key > pb.first.key   # b has the earlier atom
        pa.second == pb.second || return pa.second < pb.second
    end
    length(a.fs) < length(b.fs)
end
lead_term(s::Sum) = reduce((x, y) -> mono_lt(x.first, y.first) ? y : x, collect(s.t))

# (c, p) with s = c p^2, c > 0 and p of leading coefficient 1, or nothing: the square
# root of a polynomial, term by term from its leading one
function sqrt_poly(s::Sum)
    (2 <= length(s.t) <= 64) || return nothing
    m0, c0 = lead_term(s)
    c0 > 0 || return nothing
    r1 = powMono(m0, Q(1) // 2)
    t = scaleS(s, inv(c0))
    root = monoS(r1, Q(1))
    R = subS(t, mulS(root, root))
    for _ in 1:length(s.t)
        isempty(R.t) && return c0, root
        m, c = lead_term(R)
        nm = mulMono(m, powMono(r1, Q(-1)))
        mono_lt(nm, r1) || return nothing
        term = monoS(nm, c / 2)
        R = subS(R, addS(scaleS(mulS(root, term), Q(2)), mulS(term, term)))
        root = addS(root, term)
    end
    isempty(R.t) ? (c0, root) : nothing
end
