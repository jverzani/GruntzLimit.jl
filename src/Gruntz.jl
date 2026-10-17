"""
    Gruntz

Limits of univariate real expressions using Gruntz's algorithm
(D. Gruntz, "On Computing Limits in a Symbolic Manipulation System", 1996).

Expressions are symbolic terms implementing the TermInterface.jl methods `iscall`,
`operation` and `arguments`, with operations that are Julia `Function`s. Tested
targets are SimpleExpressions.jl, SymEngine.jl (`Basic`), SymbolicUtils.jl and
Julia's `Expr`:

    using SimpleExpressions
    @symbolic x
    gruntz_limit(sin(x)/x, x, 0)          # 1
    gruntz_limit(x^2 * exp(-x), x)        # 0
    gruntz_limit(x^2 + 1, x, -Inf)        # Inf

    import SymEngine; SymEngine.@vars y
    gruntz_limit(atan(y)/y, y, 0)         # 1

    gruntz_limit(f, x, x0 = Inf; dir = :+, build = (op, args...) -> op(args...), lift = auto, signs = ())

* `f` is the expression, `x` the symbolic variable (the same object used in `f`).
* `x0` may be `Inf`, `-Inf`, or a finite number / term not containing `x`.
* `dir` is `:+`, `:-` or `:both` (only relevant for finite `x0`).
* Returns `Inf`, `-Inf`, an `Int`/`Rational`, or a term. Non-rational results are
  rebuilt by *calling the operations as functions* (`+`, `*`, `^`, `exp`, `log`,
  `sin`, `cos`) on the pieces; with a symbolic variable inside that gives a
  symbolic term back. Constant results such as `-π/2` or `exp(1)` stay symbolic
  too: for SimpleExpressions they are built as unevaluated terms (evaluate with
  `r()`), for SymEngine they use `Basic` constants, and for `Expr` input (`x` a
  `Symbol`) results are unevaluated `Expr` calls such as `:(exp(1))`.
  Pass `build` to construct results differently (e.g. `maketerm`-based). `lift`
  converts plain numbers/π into the package's number type; by default it is the
  constructor of `typeof(f)` when that is a non-`Real` `Number` such as `Basic`,
  so a SymEngine limit of exp(1) comes back as `E`, not a float.

Operations understood (given as `Function`s; `Symbol` names are accepted too):
`+ - * / ^ inv sqrt cbrt exp log abs`, `sin cos tan sec csc cot`, their inverses
`asin acos atan asec acsc acot`, the hyperbolic `sinh cosh tanh sech csch coth` and
their inverses `asinh acosh atanh asech acsch acoth`. Limits that do not
exist because of bounded oscillation (e.g. `sin(x)` at Inf) raise `GruntzError`.

Design: terms are converted to an internal canonical form (sums of monomials with
rational coefficients/exponents over "atoms": variables, exp/log/sin/cos
applications and multi-term bases). That supplies the zero recognition Gruntz's
algorithm needs without depending on a particular CAS.
"""
module Gruntz

using TermInterface: iscall, operation, arguments, maketerm

export gruntz_limit, GruntzError

const Q = Rational{BigInt}
const HUGE = Q(10)^12   # "exact" precision marker for power series

"""
    GruntzError(msg)

Thrown by [`gruntz_limit`](@ref) when a limit cannot be computed: the limit does not
exist (bounded oscillation such as `sin(x)` at `Inf`, or one-sided limits that differ
with `dir = :both`), the expression uses an unsupported function, or the
algorithm as implemented cannot finish (e.g. the sign of a constant involving a free
parameter cannot be decided).
"""
struct GruntzError <: Exception
    msg::String
end
Base.showerror(io::IO, e::GruntzError) = print(io, "GruntzError: ", e.msg)

struct NeedMorePrecision <: Exception end
# An infinite limit. The sign is 0 when it depends on a free parameter (e.g.
# a*log(x) as x -> oo): enough to classify exp(a*log(x)) in the mrv set, where only
# finiteness matters. Where the sign itself is needed, `signof` throws `why`.
struct Infinity
    sign::Int
    why::String
end
Infinity(s::Int) = Infinity(s, "")
signof(L::Infinity) = L.sign == 0 ? throw(GruntzError(L.why)) : L.sign

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
    c < 0 && throw(GruntzError("complex power of a negative number"))
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
        throw(GruntzError("division by zero"))
    end
    if length(s.t) == 1
        m, c = first(s.t)
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
    monoS(Mono(Pair{Atom,Q}[baseatom(s) => q]), Q(1))
end

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
    isempty(s.t) && throw(GruntzError("log(0)"))
    if length(s.t) == 1
        m, c = first(s.t)
        c < 0 && throw(GruntzError("log of a negative number"))
        res = lograt(c)
        for (a, e) in m.fs
            res = addS(res, scaleS(logatom(a), e))
        end
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
    v === nothing ? atomS(funatom(:sin, Sum[s])) : v
end
function mkcos(s::Sum)
    isempty(s.t) && return oneS()
    q = piratio(s)
    v = q === nothing ? nothing : sinpi_exact(q + Q(1) // 2)   # cos(t) = sin(t + π/2)
    v === nothing ? atomS(funatom(:cos, Sum[s])) : v
end

# atan is odd: pull a negative sign of a single-term argument outside
function mkatan(s::Sum)
    isempty(s.t) && return zeroS()
    if length(s.t) == 1 && first(s.t).second < 0
        return negS(mkatan(negS(s)))
    end
    atomS(funatom(:atan, Sum[s]))
end

# abs: |c*m| = |c| * abs(m); sign-normalised so abs(u) and abs(-u) coincide.
# It is eliminated before the limit is computed (see `resolve_abs`).
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

function mkfun(h::Symbol, a::Vector{Sum})
    h === :exp ? mkexp(a[1]) :
    h === :log ? mklog(a[1]) :
    h === :sin ? mksin(a[1]) :
    h === :atan ? mkatan(a[1]) :
    h === :abs ? mkabs(a[1]) :
    h === :cos ? mkcos(a[1]) : throw(GruntzError("unsupported function $h"))
end

function mkpow(a::Sum, b::Sum)
    r = ratconst(b)
    r !== nothing ? powS(a, r) : mkexp(mulS(b, mklog(a)))
end

# --- substitution --------------------------------------------------------------
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

# --- numeric evaluation (for signs of constants) -----------------------------
# Real numbers convert directly. Other `Number` leaves (e.g. SymEngine's `Basic`
# constants) are tried through Float64; anything that is not a finite number is a
# free symbol, whose sign cannot be decided.
const FREE_SYMBOL_SIGN = "cannot decide the sign of an expression containing the free symbol"

function leaf_big(h)
    h isa Real && return BigFloat(h)
    for conv in (BigFloat, Float64)
        try
            v = BigFloat(conv(h))
            isfinite(v) && return v
        catch
        end
    end
    throw(GruntzError(FREE_SYMBOL_SIGN * " `$h`"))
end

function numval(a::Atom)
    if a.kind === :leaf
        return leaf_big(a.head)
    elseif a.kind === :base
        return numval(a.args[1]::Sum)
    end
    v = numval(a.args[1]::Sum)
    a.head === :exp ? exp(v) : a.head === :log ? log(v) : a.head === :sin ? sin(v) :
    a.head === :atan ? atan(v) : a.head === :abs ? abs(v) : cos(v)
end
function numval(s::Sum)
    acc = BigFloat(0)
    for (m, c) in s.t
        v = BigFloat(numerator(c)) / BigFloat(denominator(c))
        for (a, e) in m.fs
            v *= numval(a)^(BigFloat(numerator(e)) / BigFloat(denominator(e)))
        end
        acc += v
    end
    acc
end
# Signs of free parameters given with `gruntz_limit(...; signs)`, by leaf key.
# Experimental.
const SIGNS = Ref(Dict{String,Int}())

# The sign of a constant with free parameters, from the signs given for them: each
# term's sign is that of its coefficient times its factors' (exp(u) > 0, numbers by
# value); the constant's sign is decided only when every term has the same sign.
# Returns ±1 or `nothing`.
function infer_sign(s::Sum)
    isempty(SIGNS[]) && return nothing
    sg = 0
    for (m, c) in s.t
        t = Int(sign(c))
        for (a, e) in m.fs
            sa = atom_sign(a)
            sa === nothing && return nothing
            if sa < 0
                isone(denominator(e)) || return nothing
                isodd(numerator(e)) && (t = -t)
            end
        end
        sg == 0 ? (sg = t) : (sg == t || return nothing)
    end
    sg == 0 ? nothing : sg
end
function atom_sign(a::Atom)
    a.kind === :leaf && haskey(SIGNS[], a.key) && return SIGNS[][a.key]
    a.kind === :fun && a.head === :exp && return 1
    a.kind === :fun && a.head === :abs && return 1      # parameters are taken to be nonzero
    a.kind === :base && return infer_sign(a.args[1]::Sum)
    v = try
        numval(a)
    catch
        return nothing
    end
    abs(v) < big"1e-60" ? nothing : (v > 0 ? 1 : -1)
end

function csign(s::Sum)::Int
    isempty(s.t) && return 0
    r = ratconst(s)
    r !== nothing && return Int(sign(r))
    v = try
        numval(s)
    catch err
        err isa GruntzError || throw(GruntzError("cannot evaluate constant $(skey(s))"))
        sg = infer_sign(s)
        sg === nothing ? rethrow() : return sg
    end
    abs(v) < big"1e-60" ? 0 : (v > 0 ? 1 : -1)
end

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

struct PS
    c::Dict{Ex,Sum}   # exponent -> nonzero coefficient (an x-expression)
    prec::Ex         # exact for exponents < prec
end
val(a::PS) = isempty(a.c) ? a.prec : minimum(keys(a.c))
onePS() = PS(Dict{Ex,Sum}(EX0 => oneS()), HUGE_EX)

function trunc_ps(c::Dict{Ex,Sum}, prec::Ex)
    d = Dict{Ex,Sum}()
    for (k, v) in c
        (k < prec && !isempty(v.t)) && (d[k] = v)
    end
    PS(d, prec)
end
function addPS(a::PS, b::PS)
    c = copy(a.c)
    for (k, v) in b.c
        c[k] = haskey(c, k) ? addS(c[k], v) : v
    end
    trunc_ps(c, min(a.prec, b.prec))
end
scalePS(a::PS, s::Sum) = trunc_ps(Dict{Ex,Sum}(k => mulS(v, s) for (k, v) in a.c), a.prec)
shiftPS(a::PS, d::Ex) = PS(Dict{Ex,Sum}(k + d => v for (k, v) in a.c), a.prec + d)
function mulPS(a::PS, b::PS)
    prec = min(a.prec + val(b), b.prec + val(a))
    c = Dict{Ex,Sum}()
    for (ka, ca) in a.c, (kb, cb) in b.c
        k = ka + kb
        k >= prec && continue
        v = mulS(ca, cb)
        c[k] = haskey(c, k) ? addS(c[k], v) : v
    end
    trunc_ps(c, prec)
end

binomq(q::Q, k::Int) = (r = one(Q); for j in 0:k-1; r *= (q - j) // (j + 1); end; r)

# sum_{k>=kmin} coef(k) u^k, u having positive valuation; relative target `Trel`
function polyPS(u::PS, coef, kmin::Int, Trel::Q)
    acc = PS(Dict{Ex,Sum}(), min(Ex(Trel), u.prec))
    v = val(u)
    K = isempty(u.c) ? kmin : max(kmin, Int(israt(v) ? ceil(BigInt, Trel / v.q) : ceil(BigInt, BigFloat(Trel) / value(v))))
    pw = onePS()
    for k in 0:K
        if k >= kmin
            ck = coef(k)
            iszero(ck) || (acc = addPS(acc, scalePS(pw, constS(ck))))
        end
        k < K && (pw = mulPS(pw, u))
    end
    acc
end

# a = c0 * w^v * (1 + r); returns (v, c0, r)
function split_lead(a::PS)
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
    a.prec <= EX0 && throw(NeedMorePrecision())
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

constPS(s::Sum) = PS(isempty(s.t) ? Dict{Ex,Sum}() : Dict{Ex,Sum}(EX0 => s), HUGE_EX)

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

function logPS(a::PS, logw::Sum, P::Q)
    v, c0, r = split_lead(a)
    L = polyPS(r, k -> Q((-1)^(k + 1)) // k, 1, P)
    cst = addS(mklog(c0), mulS(logw, toS(v)))
    addPS(L, constPS(cst))
end

function series_atom(a::Atom, w::Atom, logw::Sum, P::Q, x::Atom)
    a.kind === :leaf && return PS(Dict{Ex,Sum}((a == w ? EX1 : Ex(Q(0), a.head::Sum)) => oneS()), HUGE_EX)
    a.kind === :base && return series(a.args[1]::Sum, w, logw, P, x)
    arg = series(a.args[1]::Sum, w, logw, P, x)
    h = a.head
    h === :exp ? expPS(arg, P) :
    h === :log ? logPS(arg, logw, P) :
    h === :atan ? atanPS(arg, x, P) :
    h === :sin ? trigPS(arg, P)[1] : trigPS(arg, P)[2]
end

function series(s::Sum, w::Atom, logw::Sum, P::Q, x::Atom)::PS
    acc = PS(Dict{Ex,Sum}(), HUGE_EX)     # inexact terms carry their own precision
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
# would give a wrong limit.
function numzero(s::Sum, x::Atom)
    hasleaf(s, x.key) && return false
    v = try
        numval(s)
    catch
        return false
    end
    abs(v) < big"1e-60"
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

# ---------------------------------------------------------------------------
# Gruntz's algorithm
# ---------------------------------------------------------------------------
const DEPTH = Ref(0)

function limitinf(e::Sum, x::Atom)::Union{Sum,Infinity}
    hasleaf(e, x.key) || return e
    DEPTH[] > 120 && throw(GruntzError("recursion limit reached: the expression is too " *
                                       "complicated for the algorithm as implemented"))
    DEPTH[] += 1
    try
        c0, e0 = mrv_leadterm(e, x)
        if sign(e0) > 0
            zeroS()
        elseif sign(e0) < 0
            s = try
                sgn(c0, x)
            catch err
                (err isa GruntzError && startswith(err.msg, FREE_SYMBOL_SIGN)) || rethrow()
                return Infinity(0, err.msg)
            end
            s == 0 && throw(GruntzError("could not determine the sign of the leading coefficient"))
            Infinity(s)
        else
            skey(c0) == skey(e) &&
                throw(GruntzError("no progress: leading coefficient equals the expression"))
            limitinf(c0, x)
        end
    finally
        DEPTH[] -= 1
    end
end

# sign of e as x -> +oo (nonzero for nonzero e)
function sgn(c::Sum, x::Atom)::Int
    hasleaf(c, x.key) || return csign(c)
    if length(c.t) == 1
        m, co = first(c.t)
        sg = co < 0 ? -1 : 1
        simple = true
        for (a, e) in m.fs
            if hasleaf(a, x.key)
                if !(a == x || (a.kind === :fun && a.head === :exp))
                    simple = false
                    break
                end
            else
                s2 = csign(atomS(a))
                s2 == 0 && throw(GruntzError("zero constant factor"))
                if s2 < 0
                    isone(denominator(e)) || throw(GruntzError("complex power"))
                    isodd(numerator(e)) && (sg = -sg)
                end
            end
        end
        simple && return sg
    end
    L = limitinf(c, x)
    L isa Infinity && return signof(L)
    v = csign(L)
    v != 0 && return v
    c1, _ = mrv_leadterm(c, x)
    sgn(c1, x)
end

logof(a::Atom) = (a.kind === :fun && a.head === :exp) ? a.args[1]::Sum : mklog(atomS(a))

function compare(a::Atom, b::Atom, x::Atom)
    c = limitinf(mulS(logof(a), powS(logof(b), Q(-1))), x)
    c isa Infinity ? :gt : (iszero(c) ? :lt : :eq)
end

function mrv_max(f::Vector{Atom}, g::Vector{Atom}, x::Atom)
    isempty(f) && return g
    isempty(g) && return f
    any(a -> a in g, f) && return union(f, g)
    c = compare(f[1], g[1], x)
    c === :gt ? f : c === :lt ? g : union(f, g)
end

function mrv(e::Sum, x::Atom)::Vector{Atom}
    Ω = Atom[]
    hasleaf(e, x.key) || return Ω
    for m in keys(e.t), (a, _) in m.fs
        Ω = mrv_max(Ω, mrv_atom(a, x), x)
    end
    Ω
end

function mrv_atom(a::Atom, x::Atom)::Vector{Atom}
    hasleaf(a, x.key) || return Atom[]
    a.kind === :leaf && return Atom[a]
    a.kind === :base && return mrv(a.args[1]::Sum, x)
    if a.head === :exp
        u = a.args[1]::Sum
        L = limitinf(u, x)
        return L isa Infinity ? mrv_max(Atom[a], mrv(u, x), x) : mrv(u, x)
    end
    Ω = Atom[]
    for u in a.args
        Ω = mrv_max(Ω, mrv(u::Sum, x), x)
    end
    Ω
end

function single_atom(s::Sum)
    length(s.t) == 1 || return nothing
    m, c = first(s.t)
    (isone(c) && length(m.fs) == 1) ? m.fs[1].first : nothing
end

# returns (c0, e0) with e = c0 * w^e0 + ..., w -> 0+ the exponential of the mrv class
function mrv_leadterm(e::Sum, x::Atom)
    Ω = mrv(e, x)
    isempty(Ω) && return e, EX0
    if any(==(x), Ω)
        # move up: x -> exp(x). The mrv set is mapped, never recomputed (avoids infinite recursion).
        xup = mkexp(atomS(x))
        up = a -> a == x ? xup : nothing
        newΩ = Atom[]
        ok = true
        for a in Ω
            at = single_atom(subs_atoms(atomS(a), up))
            (at === nothing || at.kind !== :fun || at.head !== :exp) ? (ok = false) : push!(newΩ, at)
        end
        e = subs_atoms(e, up)
        Ω = ok ? newΩ : mrv(e, x)
        any(==(x), Ω) && throw(GruntzError("internal error while moving up"))
    end
    sort!(Ω; by = a -> length(a.key))
    g1 = Ω[1].args[1]::Sum
    σ = sgn(g1, x)
    wS = atomS(WLEAF)
    wpow = Dict{String,Sum}()      # exp(g_i) = w^(-σ c_i) * exp(g_i - c_i g_1)
    rest = Dict{String,Sum}()      # g_i - c_i g_1
    for a in Ω
        gi = a.args[1]::Sum
        ci = limitinf(mulS(gi, powS(g1, Q(-1))), x)
        ci isa Infinity && throw(GruntzError("internal error: mrv class is inconsistent"))
        cq = ratconst(ci)
        iszero(ci) && throw(GruntzError("internal error: mrv class is inconsistent"))
        if cq === nothing      # an irrational ratio: w^(-σ ci) is a leaf of its own
            wpow[a.key] = atomS(wpowatom(scaleS(ci, Q(-σ))))
            rest[a.key] = subS(gi, mulS(g1, ci))
        else
            wpow[a.key] = powS(wS, Q(-σ) * cq)
            rest[a.key] = subS(gi, scaleS(g1, cq))
        end
    end
    # The factor exp(g_i - c_i g_1) may itself contain members of Ω inside its
    # argument (e.g. exp(exp(-x)) = exp(w)), so it is rewritten recursively.
    memo = Dict{String,Sum}()
    function rewrite(a::Atom)
        haskey(wpow, a.key) || return nothing
        haskey(memo, a.key) && return memo[a.key]
        v = mulS(wpow[a.key], subs_atoms(mkexp(rest[a.key]), rewrite))
        memo[a.key] = v
        v
    end
    f = subs_atoms(e, rewrite)
    leadterm(f, WLEAF, scaleS(g1, Q(-σ)), x)   # log(w) = -σ g1
end

# ---------------------------------------------------------------------------
# TermInterface <-> canonical form
# ---------------------------------------------------------------------------
function from_number(t)
    t isa Integer && return constS(Q(t))
    t isa Rational && return constS(Q(t))
    if t isa AbstractIrrational
        return t === ℯ ? mkexp(oneS()) : atomS(leafatom(t))
    end
    if t isa AbstractFloat
        isfinite(t) || throw(GruntzError("non-finite number in expression"))
        return constS(rationalize(BigInt, t))
    end
    t isa Complex && throw(GruntzError("complex numbers are not supported"))
    atomS(leafatom(t))          # symbolic wrapper types (e.g. Num) that are leaves
end

safe_iscall(t) = try iscall(t) === true catch; false end

const NAMED_CONSTANTS = Dict{String,Any}(
    "pi" => π, "π" => π, "E" => ℯ, "ℯ" => ℯ, "exp(1)" => ℯ,   # SymEngine prints E as exp(1)
    "EulerGamma" => Base.MathConstants.eulergamma,
    "Catalan" => Base.MathConstants.catalan,
    "GoldenRatio" => Base.MathConstants.golden)

# A leaf that is a callable constant (e.g. a symbolic number) is evaluated; a
# variable or parameter cannot be called with no arguments and stays an atom.
function leaf_value(t)
    t isa Function || return nothing
    try
        v = t()
        v isa Real ? v : nothing
    catch
        nothing
    end
end

# Numeric leaves of symbolic packages that are not Julia numbers (e.g. SymEngine's
# `Basic` integers, rationals, floats and named constants such as `E`, `pi`, or
# SymbolicUtils' constants, which print like `2` or `(10//3)`) are recognised
# through their printed form, which is exact and package independent. Only the
# unambiguous names `π` and `ℯ` are taken as constants for leaves that are not
# `Number`s, where a name like `E` could be a variable. Returns a `Sum`, or
# `nothing` for a symbol.
function leaf_number(t)
    if t isa Function
        v = leaf_value(t)
        return v === nothing ? nothing : from_number(v)
    end
    t isa Symbol && return nothing      # an `Expr` variable
    s = string(t)
    m = match(r"^\((.*)\)$", s)
    m === nothing || (s = m.captures[1])
    m = match(r"^(-?\d+)(?:/{1,2}(\d+))?$", s)
    if m !== nothing
        n = parse(BigInt, m.captures[1])
        d = m.captures[2] === nothing ? big(1) : parse(BigInt, m.captures[2])
        return constS(Q(n // d))
    end
    if occursin(r"^-?(\d+\.\d*|\.\d+|\d+)([eE][+-]?\d+)?$", s)
        return constS(rationalize(BigInt, parse(Float64, s)))
    end
    (t isa Number || s in ("π", "ℯ")) || return nothing
    haskey(NAMED_CONSTANTS, s) ? from_number(NAMED_CONSTANTS[s]) : nothing
end

# Constants written as bare symbols in a Julia `Expr`, e.g. :(pi * x)
const EXPR_CONSTANTS = Dict{Symbol,Any}(:pi => π, :π => π, :ℯ => ℯ)

function from_term(t)::Sum
    if safe_iscall(t)
        args = arguments(t)
        isempty(args) || return apply_op(operation(t), Sum[from_term(a) for a in args])
    end
    t isa Union{Integer,Rational,AbstractFloat,AbstractIrrational,Complex} && return from_number(t)
    t isa Symbol && haskey(EXPR_CONSTANTS, t) && return from_number(EXPR_CONSTANTS[t])
    v = leaf_number(t)
    v === nothing ? atomS(leafatom(t)) : v
end

# Functions rewritten in terms of others: f(u) = 1/RECIPROCALS[f](u) and
# f(u) = INVERSES[f](1/u) (Julia's definitions of asec, acsc, acot, ...).
const RECIPROCALS = Dict(:sec => :cos, :csc => :sin, :cot => :tan,
                         :sech => :cosh, :csch => :sinh, :coth => :tanh)
const INVERSES = Dict(:asec => :acos, :acsc => :asin, :acot => :atan,
                      :asech => :acosh, :acsch => :asinh, :acoth => :atanh)

function apply_op(op, a::Vector{Sum})
    n = op isa Symbol ? op : (op isa Function ? nameof(op) : Symbol(string(op)))
    na = length(a)
    half = Q(1) // 2
    if n === :identity && na == 1       # SymbolicUtils wraps constants such as π
        a[1]
    elseif n === :+
        foldl(addS, a; init = zeroS())
    elseif n === :-
        na == 1 ? negS(a[1]) : subS(a[1], foldl(addS, a[2:end]; init = zeroS()))
    elseif n === :*
        foldl(mulS, a; init = oneS())
    elseif n in (:/, ://) && na == 2                  # `//` from rational literals in an `Expr`
        mulS(a[1], powS(a[2], Q(-1)))
    elseif n === :inv && na == 1
        powS(a[1], Q(-1))
    elseif n === :^ && na == 2
        mkpow(a[1], a[2])
    elseif n === :sqrt && na == 1
        powS(a[1], half)
    elseif n === :cbrt && na == 1
        powS(a[1], Q(1) // 3)
    elseif n === :exp && na == 1
        mkexp(a[1])
    elseif n === :log && na == 1
        mklog(a[1])
    elseif n === :log && na == 2
        mulS(mklog(a[2]), powS(mklog(a[1]), Q(-1)))
    elseif n === :atan && na == 1
        mkatan(a[1])
    elseif n === :abs && na == 1
        mkabs(a[1])
    elseif n === :sin && na == 1
        mksin(a[1])
    elseif n === :cos && na == 1
        mkcos(a[1])
    elseif n === :tan && na == 1
        mulS(mksin(a[1]), powS(mkcos(a[1]), Q(-1)))
    elseif n in (:sinh, :cosh, :tanh) && na == 1
        p, m = mkexp(a[1]), mkexp(negS(a[1]))
        s = scaleS(subS(p, m), half)
        c = scaleS(addS(p, m), half)
        n === :sinh ? s : n === :cosh ? c : mulS(s, powS(c, Q(-1)))
    elseif haskey(RECIPROCALS, n) && na == 1
        powS(apply_op(RECIPROCALS[n], a), Q(-1))      # sec = 1/cos, coth = 1/tanh, ...
    elseif n === :asin && na == 1                     # asin(u) = atan(u / sqrt(1 - u^2))
        mkatan(mulS(a[1], powS(subS(oneS(), mulS(a[1], a[1])), -half)))
    elseif n === :acos && na == 1                     # acos(u) = π/2 - asin(u)
        subS(scaleS(atomS(PI_ATOM), half), apply_op(:asin, a))
    elseif n in (:asec, :acsc, :acot) && na == 1      # asec(u) = acos(1/u), ...
        apply_op(INVERSES[n], Sum[powS(a[1], Q(-1))])
    elseif n === :asinh && na == 1                    # log(u + sqrt(u^2 + 1))
        mklog(addS(a[1], powS(addS(mulS(a[1], a[1]), oneS()), half)))
    elseif n === :acosh && na == 1                    # log(u + sqrt(u^2 - 1))
        mklog(addS(a[1], powS(subS(mulS(a[1], a[1]), oneS()), half)))
    elseif n === :atanh && na == 1                    # log((1 + u)/(1 - u)) / 2
        scaleS(subS(mklog(addS(oneS(), a[1])), mklog(subS(oneS(), a[1]))), half)
    elseif n in (:asech, :acsch, :acoth) && na == 1   # asech(u) = acosh(1/u), ...
        apply_op(INVERSES[n], Sum[powS(a[1], Q(-1))])
    else
        throw(GruntzError("unsupported function/operator `$n` with $na argument(s)"))
    end
end

const OPS = Dict{Symbol,Function}(:+ => +, :* => *, :^ => ^, :exp => exp, :log => log,
                                  :sin => sin, :cos => cos, :atan => atan, :abs => abs,
                                  :sqrt => sqrt)
default_build(op, args...) = op(args...)

# Build `op(args...)` for constant arguments WITHOUT evaluating it, for symbolic
# types that defer evaluation only when a symbolic variable is involved
# (SimpleExpressions). Plain Julia would turn e.g. sqrt(2) or (-1//2)*π into a
# Float64 at once. Strategies, in order:
#  1. placeholder substitution: build op(x, args[2:end]...) with the symbolic
#     variable `x` as first argument, then substitute args[1] for it with
#     `u(args[1], :)`, which SimpleExpressions documents as leaving a symbolic
#     expression (evaluated later with `u()`);
#  2. TermInterface's `maketerm`, trying both conventions for `head`;
#  3. evaluating eagerly (the result is then a plain number).
function placeholder_call(x, op, args)
    isempty(args) && return nothing
    try
        u = op(x, args[2:end]...)
        u isa Function || return nothing
        r = u(args[1], :)
        r isa Function ? r : nothing
    catch
        nothing
    end
end

function maketerm_call(T, op, args)
    for TT in unique(Any[T, Base.typename(T).wrapper])
        for attempt in (() -> maketerm(TT, op, Any[args...], nothing),
                        () -> maketerm(TT, :call, Any[op; args...], nothing))
            try
                r = attempt()
                r isa Function && return r
            catch
            end
        end
    end
    nothing
end

function deferred_call(x, op, args)
    r = placeholder_call(x, op, args)
    r === nothing || return r
    r = maketerm_call(typeof(x), op, args)
    r === nothing || return r
    op(args...)
end

expr_build(op, args...) = Expr(:call, nameof(op), args...)

# Term types that are neither numbers nor callable (SymbolicUtils): a call on
# plain numbers only is built with `maketerm` for the type of the variable, which
# keeps it unevaluated (sqrt(2), not 1.414…). A power of a number with exponent
# p/2 or p/3 is built from sqrt or cbrt, as such types may fold numeric powers to
# floats. Anything else applies the operation.
function term_build(x)
    T = typeof(x)
    mt(op, args) = (r = try maketerm(T, op, Any[args...], nothing) catch; nothing end; r isa T ? r : nothing)
    function build(op, args...)
        all(a -> a isa Number, args) || return op(args...)
        if op === (^) && length(args) == 2
            n, e = args
            if e isa Integer && n isa Union{Integer,Rational}
                return num(Q(n)^e)
            elseif e isa Rational && denominator(e) in (2, 3)
                root = mt(denominator(e) == 2 ? sqrt : cbrt, Any[n])
                root === nothing || return isone(numerator(e)) ? root : root^numerator(e)
            end
        end
        r = mt(op, args)
        r === nothing ? op(args...) : r
    end
end

# A constant such as π is turned into a term of the variable's type through
# `maketerm(T, identity, [π])` (how SymbolicUtils represents it), else left as is.
function term_lift(x)
    T = typeof(x)
    v -> v isa AbstractIrrational ?
         (r = try maketerm(T, identity, Any[v], nothing) catch; nothing end; r isa T ? r : v) : v
end

# A term type that is neither a Julia number (SymEngine), callable
# (SimpleExpressions) nor a `Symbol` (`Expr`), e.g. SymbolicUtils.
other_terms(x) = !(x isa Number || x isa Function || x isa Symbol)

# Default builder. Julia `Expr`s (variable given as a `Symbol`) are built as
# unevaluated calls, so results stay exact and may contain parameters.
# Function-like symbolic types (SimpleExpressions) defer evaluation only when
# some argument is symbolic; for constant-only terms we construct the node
# explicitly. Numeric types (e.g. SymEngine's `Basic`) simply apply the
# operation, which stays symbolic through their own number type. Other term
# types use `term_build`.
function auto_build(f, x)
    x isa Symbol && return expr_build
    other_terms(x) && return term_build(x)
    typeof(x) <: Function || return default_build
    (op, args...) -> any(a -> a isa Function, args) ? op(args...) : deferred_call(x, op, args)
end

# `build(op, args...)` constructs a compound term; `lift(v)` turns plain Julia
# numbers (and π) into the symbolic package's own number type.
struct Builder
    build::Any
    lift::Any
end
mk(bd::Builder, name::Symbol, args) = bd.build(OPS[name], args...)

fitint(n::BigInt) = typemin(Int) <= n <= typemax(Int) ? Int(n) : n
function num(c::Q)
    n, d = numerator(c), denominator(c)
    isone(d) && return fitint(n)
    (typemin(Int) <= n <= typemax(Int) && d <= typemax(Int)) ? Int(n) // Int(d) : c
end

atom_term(b, a::Atom) =
    a.kind === :leaf ? (a.head isa AbstractIrrational ? b.lift(a.head) : a.head) :
    a.kind === :base ? to_term(b, a.args[1]::Sum) :
    mk(b, a.head, Any[to_term(b, a.args[1]::Sum)])

function mono_term(b, m::Mono, c::Q)
    fs = Any[]
    for (a, e) in m.fs
        t = atom_term(b, a)
        push!(fs, isone(e) ? t : e == Q(1) // 2 ? mk(b, :sqrt, Any[t]) :
                  mk(b, :^, Any[t, b.lift(num(e))]))
    end
    isempty(fs) && return b.lift(num(c))
    isone(c) && return length(fs) == 1 ? fs[1] : mk(b, :*, fs)
    mk(b, :*, Any[b.lift(num(c)); fs])
end

function to_term(b, s::Sum)
    isempty(s.t) && return b.lift(0)
    ts = Any[mono_term(b, m, c) for (m, c) in sort!(collect(s.t); by = p -> p.first.key)]
    length(ts) == 1 ? ts[1] : mk(b, :+, ts)
end

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
function lim_equal(a, b)
    (a isa Infinity && b isa Infinity) && return signof(a) == signof(b)
    (a isa Sum && b isa Sum) && return skey(a) == skey(b)
    false
end

# +1 / -1 for +/-infinity (Julia floats or a symbolic package's infinity), else 0
function with_signs(g, signs)
    d = Dict{String,Int}()
    for (p, sg) in signs
        sg in (1, -1) || throw(ArgumentError("the sign of `$p` must be 1 or -1, got $sg"))
        d[leafatom(p).key] = sg
    end
    old = SIGNS[]
    SIGNS[] = d
    try
        g()
    finally
        SIGNS[] = old
    end
end

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
            err isa GruntzError ? nothing : rethrow()
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
        lim_equal(l, r) || throw(GruntzError("one-sided limits differ"))
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
* `signs` (**experimental**, may change): the signs of free parameters, as pairs
  `parameter => 1` or `parameter => -1` (e.g. `Dict(a => 1)`), for limits that depend on
  them, such as `x^a`. A parameter is otherwise taken to be nonzero, of unknown sign.
  The sign of an expression in the parameters is decided only when every term of it has
  the same sign (so `2a + b` with `a, b > 0`, but not `a - 2`).

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
    L = with_signs(signs) do
        _limit(from_term(f), leafatom(x), x0, dir)
    end
    L isa Infinity && return signof(L) > 0 ? Inf : -Inf
    r = ratconst(L)
    r !== nothing && return num(r)
    to_term(Builder(build === nothing ? auto_build(f, x) : build,
                    lift === nothing ? auto_lift(f, x) : lift), L)
end

end # module
