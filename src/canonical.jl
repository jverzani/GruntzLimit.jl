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
function mulS(a::Sum, b::Sum)
    d = Dict{Mono,Q}()
    for (m1, c1) in a.t, (m2, c2) in b.t
        m = mulMono(m1, m2)
        v = get(d, m, zero(Q)) + c1 * c2
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
        if c < 0 && !isone(denominator(q))
            np = negparam(m, c)
            if np !== nothing
                k, r = np
                kr = mulMono(Mono(Pair{Atom,Q}[baseatom(k) => q]), powMono(r, q))
                return mulS(powS(constS(-c), q), monoS(kr, Q(1)))
            end
        end
        mm = powMono(m, q)
        r = ratpow(c, q)
        if r === nothing
            mm = mulMono(mm, Mono(Pair{Atom,Q}[baseatom(constS(c)) => q]))
            r = Q(1)
        end
        return monoS(mm, r)
    end
    if isone(denominator(q)) && 0 < q <= 8
        res = s
        for _ in 2:Int(q)
            res = mulS(res, s)
        end
        return res
    end
    !isone(denominator(q)) && require_positive(s; strict = q < 0, what = "fractional power")
    monoS(Mono(Pair{Atom,Q}[baseatom(s) => q]), Q(1))
end
