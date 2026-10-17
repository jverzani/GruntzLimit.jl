const T_START = time()
using GruntzLimit
include("su_common.jl")
LIMIT(f, x, x0, dir) = gruntz_limit(f, x, x0; dir)
SOLVED(out) = true  # failures throw
include("core.jl")
