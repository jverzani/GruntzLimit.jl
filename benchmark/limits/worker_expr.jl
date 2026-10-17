const T_START = time()
using GruntzLimit
const VAR = Dict{Symbol,Any}(v => v for v in (:x, :a, :b, :π, :ℯ))
LIMIT(f, x, x0, dir) = gruntz_limit(f, x, x0; dir)
SOLVED(out) = true  # failures throw
BUILD(ex) = ex      # the problem's quoted expression is the term
# evaluate by replacing each parameter with its value, then evaluating the Expr
subst(ex, vals) = ex isa Symbol ? get(vals, ex, ex) :
    ex isa Expr ? Expr(ex.head, (subst(a, vals) for a in ex.args)...) : ex
function EVAL(ex, vals)
    u = Core.eval(Main, subst(ex, vals))
    isa(u, Number) ? u : nothing
end
include("core.jl")
