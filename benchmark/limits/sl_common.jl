# SymbolicLimits' `limit(expr, var, h[, side])` returns (value, assumptions);
# its sides are :left, :right and :both, and none is given at ±Inf
using SymbolicLimits
include("su_common.jl")
const SIDE = Dict(:+ => :right, :- => :left, :both => :both)
const ASSUMPTIONS = Ref{Any}(nothing)
function LIMIT(f, x, x0, dir)
    v, as = x0 isa Real && isinf(x0) ? SymbolicLimits.limit(f, x, x0) :
        SymbolicLimits.limit(f, x, x0, SIDE[dir])
    ASSUMPTIONS[] = as
    v
end
SOLVED(out) = !has_x(out)
NOTE() = (as = filter(!isequal(true), collect(ASSUMPTIONS[])); isempty(as) ? "" : " (assuming " * join(string.(as), ", ") * ")")
