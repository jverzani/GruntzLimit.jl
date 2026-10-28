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

function numval(a::Atom)
    if a.kind === :leaf
        return leaf_big(a.head)
    elseif a.kind === :base
        return numval(a.args[1]::Sum)
    end
    v = numval(a.args[1]::Sum)
    a.head === :exp ? exp(v) : a.head === :log ? log(v) : a.head === :sin ? sin(v) :
    a.head === :atan ? atan(v) : a.head === :erf ? SpecialFunctions.erf(v) :
    a.head === :erfs ? SpecialFunctions.erfcx(v) : a.head === :abs ? abs(v) : a.head === :floor ? floor(v) :
    a.head === :sign ? (abs(v) < big"1e-60" ? zero(v) : sign(v)) :   # zero as `csign` decides
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
