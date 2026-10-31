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
                                       :fsi => fsi, :gsi => gsi)

function numval(a::Atom)
    if a.kind === :leaf
        return leaf_big(a.head)
    elseif a.kind === :base
        return numval(a.args[1]::Sum)
    end
    v = numval(a.args[1]::Sum)
    a.head === :exp ? exp(v) : a.head === :log ? log(v) : a.head === :sin ? sin(v) :
    a.head === :atan ? atan(v) : a.head === :erf ? SpecialFunctions.erf(v) :
    a.head === :erfs ? SpecialFunctions.erfcx(v) : a.head === :gamma ? SpecialFunctions.gamma(v) :
    a.head in keys(F64_FUNS) ? BigFloat(F64_FUNS[a.head](Float64(v))) :
    a.head === :lgrem ? SpecialFunctions.loggamma(v) - ((v - 1 / 2) * log(v) - v + log(2 * big(π)) / 2) : a.head === :abs ? abs(v) : a.head === :floor ? floor(v) :
    a.head === :sign ? (abs(v) < big"1e-60" ? zero(v) : sign(v)) :   # zero as `csign` decides
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
