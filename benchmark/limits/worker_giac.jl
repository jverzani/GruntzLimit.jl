# Giac's own `limit` (Giac.jl), for reference: a long-established limit algorithm
const T_START = time()
using Giac
@giac_var x a b
const VAR = Dict{Symbol,Any}(:x => x, :a => a, :b => b, :π => giac_eval("pi"), :ℯ => giac_eval("exp(1)"))
# Giac's direction is 1 (from the right) or -1 (from the left); without one, the limit
# is two-sided. Its infinite limits are +infinity and -infinity, returned as ±Inf.
const SIDE = Dict(:+ => 1, :- => -1)
function LIMIT(f, x, x0, dir)
    p = atinf(x0) ? giac_eval(x0 > 0 ? "+infinity" : "-infinity") : x0
    out = atinf(x0) || dir === :both ? Giac.Commands.limit(f, x, p) : Giac.Commands.limit(f, x, p, SIDE[dir])
    s = string(out)
    s == "+infinity" ? Inf : s == "-infinity" ? -Inf : out
end
atinf(x0) = x0 isa Real && isinf(x0)
# Giac leaves `limit(...)` unevaluated, or answers undef, an unsigned `infinity`, or
# `bounded_function(...)` (no limit) when it has none
SOLVED(out) = out isa Real || !occursin(r"limit|undef|bounded_function|^infinity$", string(out))
# The values are rounded to 12 digits: Giac misreads longer floats (see RischIntegrate's benchmark)
r12(p::Real) = round(p, sigdigits = 12)
function EVAL(ex, vals)
    u = to_julia(invoke_cmd(:evalf, Giac.substitute(ex, Dict(VAR[v] => r12(p) for (v, p) in vals))))
    isa(u, Number) ? u : nothing
end
include("core.jl")
