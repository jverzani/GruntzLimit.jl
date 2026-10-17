# The SymbolicUtils variables and evaluation, shared by the GruntzLimit and
# SymbolicLimits workers, so both get the same terms. Exact constants as in
# test/test_SymbolicUtils.jl: π as identity(π) and ℯ as exp(1) with a constant 1.
using SymbolicUtils
using SymbolicUtils: @syms
using TermInterface: iscall, arguments
@syms x::Real a::Real b::Real
const ONE = SymbolicUtils.Const{SymbolicUtils.SymReal}(1)
const PI = SymbolicUtils.maketerm(typeof(x), identity, Any[π], nothing)
const VAR = Dict{Symbol,Any}(:x => x, :a => a, :b => b, :π => PI, :ℯ => exp(ONE))
function EVAL(ex, vals)
    isa(ex, Number) && return ex
    r = SymbolicUtils.substitute(ex, Dict{Any,Any}(VAR[v] => p for (v, p) in vals); fold = Val(true))
    u = SymbolicUtils.unwrap_const(r)
    isa(u, Number) ? u : nothing
end
has_x(e) = isequal(e, x) || (iscall(e) && any(has_x, arguments(e)))
