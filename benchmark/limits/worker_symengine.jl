const T_START = time()
using GruntzLimit
using SymEngine
SymEngine.@vars x a b
const VAR = Dict{Symbol,Any}(:x => x, :a => a, :b => b, :π => SymEngine.PI, :ℯ => SymEngine.E)
LIMIT(f, x, x0, dir) = gruntz_limit(f, x, x0; dir)
SOLVED(out) = true  # failures throw
function EVAL(ex, vals)
    u = SymEngine.N(SymEngine.subs(Basic(ex), (VAR[v] => p for (v, p) in vals)...))
    isa(u, Number) ? u : nothing
end
include("core.jl")
