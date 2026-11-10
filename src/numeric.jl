# ---------------------------------------------------------------------------
# Numeric evaluation
# ---------------------------------------------------------------------------
# --- numeric evaluation (for signs of constants) -----------------------------
# Real numbers convert directly. Other `Number` leaves (e.g. SymEngine's `Basic`
# constants) are tried through Float64; anything that is not a finite number is a
# free symbol (a parameter), and `FreeSymbol` is thrown.
struct FreeSymbol <: Exception
    h::Any
end

function leaf_big(h)
    h isa Real && return BigFloat(h)
    if h isa Function            # a callable leaf answers without an exception
        v = leaf_value(h)
        v === nothing && throw(FreeSymbol(h))
        return BigFloat(v)
    end
    for conv in (BigFloat, Float64)
        try
            v = BigFloat(conv(h))
            isfinite(v) && return v
        catch
        end
    end
    throw(FreeSymbol(h))
end

# functions that SpecialFunctions evaluates in Float64 only; fsi and gsi are the
# auxiliary functions of sinint and cosint
fsi(t) = SpecialFunctions.cosint(t) * sin(t) - (SpecialFunctions.sinint(t) - π / 2) * cos(t)
gsi(t) = -SpecialFunctions.cosint(t) * cos(t) - (SpecialFunctions.sinint(t) - π / 2) * sin(t)
const F64_FUNS = Dict{Symbol,Function}(:sinint => SpecialFunctions.sinint, :cosint => SpecialFunctions.cosint,
                                       :erfi => SpecialFunctions.erfi, :dawson => SpecialFunctions.dawson,
                                       :fsi => fsi, :gsi => gsi, :expinti => SpecialFunctions.expinti,
                                       :eiaux => t -> exp(-t) * SpecialFunctions.expinti(t))

function numval(a::Atom)
    if a.kind === :leaf
        return leaf_big(a.head)
    elseif a.kind === :base
        return numval(a.args[1]::Sum)
    end
    v = numval(a.args[1]::Sum)
    if a.head in (:besselk, :kaux)
        ν, t = Float64(numval(a.args[2]::Sum)), Float64(v)
        k = SpecialFunctions.besselk(ν, t)
        return BigFloat(a.head === :besselk ? k : k / (sqrt(π / (2t)) * exp(-t)))
    elseif a.head in (:besselj, :jred)
        ν, t = Float64(numval(a.args[2]::Sum)), Float64(v)
        J = BigFloat(SpecialFunctions.besselj(ν, t))
        return a.head === :besselj ? J : J / (v / 2)^BigFloat(ν)
    elseif a.head in (:erfcxre, :erfcxim)
        w = SpecialFunctions.erfcx(complex(Float64(v), Float64(numval(a.args[2]::Sum))))
        return BigFloat(a.head === :erfcxre ? real(w) : imag(w))
    elseif a.head in (:besseli, :iaux)
        ν, t = Float64(numval(a.args[2]::Sum)), Float64(v)
        return BigFloat(a.head === :besseli ? SpecialFunctions.besseli(ν, t) :
                        SpecialFunctions.besselix(ν, t) * sqrt(2π * t))
    end
    a.head === :polygamma &&
        return BigFloat(SpecialFunctions.polygamma(Int(numval(a.args[2]::Sum)), Float64(v)))
    if a.head === :psiaux                    # ψ^(k)(v), less log(v) for k = 0
        k = Int(numval(a.args[2]::Sum))
        return BigFloat(SpecialFunctions.polygamma(k, Float64(v))) - (k == 0 ? log(v) : zero(v))
    end
    a.head === :exp ? exp(v) : a.head === :log ? log(v) : a.head === :sin ? sin(v) :
    a.head === :atan ? atan(v) : a.head === :erf ? SpecialFunctions.erf(v) :
    a.head === :erfs ? SpecialFunctions.erfcx(v) : a.head === :gamma ? SpecialFunctions.gamma(v) :
    a.head in keys(F64_FUNS) ? BigFloat(F64_FUNS[a.head](Float64(v))) :
    a.head === :lgrem ? SpecialFunctions.loggamma(v) - ((v - 1 / 2) * log(v) - v + log(2 * big(π)) / 2) : a.head === :abs ? abs(v) : a.head === :floor ? floor(v) : a.head === :fracpart ? v - floor(v) :
    a.head === :sign ? (abs(v) < big"1e-60" ? zero(v) : sign(v)) :   # zero as `csign` decides
    a.head === :clausen2 ? clausen2_big(v) : a.head === :li2 ? li2_big(v) :
    a.head === :lambertw ? lambertw_big(v) : a.head === :wexp ? wexp_big(v) :
    a.head === :cos ? cos(v) : throw(GruntzError("cannot evaluate $(a.head)"))
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
bigq(q::Q) = BigFloat(numerator(q)) / BigFloat(denominator(q))

# Does the atom contain a leaf that is certainly a free symbol? Decided without
# exceptions for callable leaves (a `throw` costs ~40 μs, for its backtrace, and atoms
# are tested often); other leaves are left to `numval`.
surely_free(h) = h isa Function && !(h isa Real) && leaf_value(h) === nothing
function surely_free(a::Atom)
    a.kind === :leaf && return surely_free(a.head)
    any(u -> any(m -> any(p -> surely_free(p.first), m.fs), keys((u::Sum).t)), a.args)
end

# the value of an atom, or nothing for an atom with parameters
function numval_or_nothing(a::Atom)
    surely_free(a) && return nothing
    try
        numval(a)
    catch err
        err isa Union{FreeSymbol,DomainError} || rethrow()
        nothing
    end
end

# Cl₂(v): v reduced to (-π, π], then v - v log|v| + Σ |B_2n| / (2n (2n+1)!) v^(2n+1),
# whose terms decrease at least like 4^(-n)
function clausen2_big(v::BigFloat)
    tp = 2 * big(π)
    t = v - tp * round(v / tp)
    iszero(t) && return t
    s = t - t * log(abs(t))
    t2, p = t * t, t
    for n in 1:2000
        p *= t2
        term = abs(BigFloat(bernoulli(2n))) / (2n * factorial(big(2n + 1))) * p
        s += term
        abs(term) <= eps(BigFloat) * abs(s) && break
    end
    s
end
clausen2(t::Real) = Float64(clausen2_big(BigFloat(t)))

# li2(v), v <= 1: Σ v^k/k² for |v| <= 1/2, reduced to that range by the reflection
# (1/2 < v <= 1), Landen (-1 <= v < -1/2) and inversion (v < -1) formulas
function li2_big(v::BigFloat)
    v > 1 && throw(DomainError(v, "li2 of a number above 1 is not real"))
    p2 = big(π)^2
    v == 1 && return p2 / 6
    v < -1 && return -p2 / 6 - log(-v)^2 / 2 - li2_big(1 / v)
    v < -0.5 && return -li2_big(v / (v - 1)) - log1p(-v)^2 / 2
    v > 0.5 && return p2 / 6 - log(v) * log1p(-v) - li2_big(1 - v)
    s, p = zero(v), one(v)
    for k in 1:100_000
        p *= v
        term = p / k^2
        s += term
        abs(term) <= eps(BigFloat) * abs(s) && break
    end
    s
end
li2(t::Real) = Float64(li2_big(BigFloat(t)))

# The principal branch of Lambert's W, for v >= -1/e, by Halley's iteration
function lambertw_big(v::BigFloat)
    v < -exp(big(-1)) && throw(DomainError(v, "lambertw of a number below -1/e"))
    iszero(v) && return v
    d = 1 + exp(big(1)) * v
    d < 10eps(BigFloat) && return big(-1)
    w = v < -big"0.25" ? sqrt(2d) - 1 : v < 3 ? log1p(v) : log(v) - log(log(v))
    for _ in 1:200
        e = exp(w)
        f = w * e - v
        wn = w - f / (e * (w + 1) - (w + 2) * f / (2w + 2))
        abs(wn - w) <= eps(BigFloat) * (1 + abs(wn)) && return wn
        w = wn
    end
    w
end
# W(exp(L)), by Newton's iteration on F + log(F) = L for large L
function wexp_big(L::BigFloat)
    L < 2 && return lambertw_big(exp(L))
    F = L - log(L)
    for _ in 1:200
        Fn = F - (F + log(F) - L) / (1 + 1 / F)
        abs(Fn - F) <= eps(BigFloat) * (1 + abs(Fn)) && return Fn
        F = Fn
    end
    F
end
