const T_START = time()
using GruntzLimit
using SymJ
const VAR = Dict{Symbol,Any}(:x => Sym(:x), :a => Sym(:a), :b => Sym(:b), :π => Sym(π), :ℯ => Sym(ℯ))
LIMIT(f, x, x0, dir) = gruntz_limit(f, x, x0; dir)
SOLVED(out) = true  # failures throw
function EVAL(ex, vals)
    ex isa Number && return ex
    u = N(subs(ex, (VAR[v] => p for (v, p) in vals)...))
    isa(u, Number) ? u : nothing
end
include("core.jl")
