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
bigq(q::Q) = BigFloat(numerator(q)) / BigFloat(denominator(q))

# the value of an atom, or nothing for an atom with parameters
function numval_or_nothing(a::Atom)
    try
        numval(a)
    catch err
        err isa Union{FreeSymbol,DomainError} || rethrow()
        nothing
    end
end
