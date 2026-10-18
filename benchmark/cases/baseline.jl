# julia --project=../limits/env_gruntz baseline.jl
# What GruntzLimit does today on problems.jl (Expr input), in two ways:
#  - without information about the parameters;
#  - for each case, with `signs` taken from the case's sample values (a parameter
#    whose sample is 0 is substituted).
# A case counts as done when the answer matches the case's (numerically, at the
# sample values) or, for :nolimit/:undefined, when a GruntzError is thrown.
using GruntzLimit
const PROBLEMS = include(joinpath(@__DIR__, "problems.jl"))

subst(ex, d) = ex isa Symbol ? get(d, ex, ex) :
    ex isa Expr ? Expr(ex.head, (subst(a, d) for a in ex.args)...) : ex
numeric(ex, vals) = Core.eval(Main, subst(ex, Dict{Symbol,Any}(pairs(vals))))

function attempt(f, x0, dir; kw...)
    try
        gruntz_limit(f, :x, x0; dir, kw...)
    catch err
        err isa GruntzError || rethrow()
        err
    end
end

function matches(r, ans, vals)
    ans in (:nolimit, :undefined) && return r isa GruntzError
    r isa GruntzError && return false
    v, w = Float64(numeric(r, vals)), Float64(numeric(ans, vals))
    isinf(w) ? v == w : isapprox(v, w; rtol = 1e-8, atol = 1e-12)
end
show_r(r) = r isa GruntzError ? "GruntzError: " * r.msg : string(r)

let ndone = 0, n = 0
    for (i, (f, x0, dir, cases, src)) in enumerate(PROBLEMS)
        println("$i. lim x → $x0 ($dir) of $f   [$src]")
        println("   no information: ", show_r(attempt(f, x0, dir)))
        for (cond, vals, ans) in cases
            zero = Dict{Symbol,Any}(k => 0 for (k, v) in pairs(vals) if iszero(v))
            signs = Dict(k => v > 0 ? :positive : :negative for (k, v) in pairs(vals) if !iszero(v))
            r = attempt(subst(f, zero), subst(x0, zero), dir; signs)
            ok = try matches(r, ans, vals) catch; false end
            n += 1; ndone += ok
            println("   ", ok ? "✓" : "✗", " ", rpad(string(cond), 24), " want ", rpad(string(ans), 10), " got ", show_r(r))
        end
    end
    println("\n$ndone of $n cases done with signs (and zeros substituted)")
end
