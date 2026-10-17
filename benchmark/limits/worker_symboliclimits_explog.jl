# SymbolicLimits on the same terms, after rewriting what it does not support
# into exp and log: sqrt(u) → exp(log(u)/2), cbrt(u) → exp(log(u)/3), and
# u^v → exp(v*log(u)) unless v is an integer. Valid where u > 0, as it is near
# the limit point in these problems.
const T_START = time()
include("sl_common.jl")
using TermInterface: operation
function explog(e)
    iscall(e) || return e
    op, args = operation(e), map(explog, arguments(e))
    op === sqrt && return exp(log(args[1]) / 2)
    op === cbrt && return exp(log(args[1]) / 3)
    if op === (^)
        n = SymbolicUtils.unwrap_const(args[2])
        n isa Real && isinteger(n) || return exp(args[2] * log(args[1]))
    end
    op(args...)
end
BUILD(ex) = explog(build(ex))
include("core.jl")
