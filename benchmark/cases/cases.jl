# julia --project=../limits/env_gruntz cases.jl
# Scores `gruntz_cases` (Expr input) on problems.jl. For each case of a problem, the
# sample values must satisfy the conditions of exactly one of the returned cases, and
# that case's limit must be the answer (numerically, at the sample values; :nolimit
# and :undefined must match exactly).
using GruntzLimit
const PROBLEMS = include(joinpath(@__DIR__, "problems.jl"))

subst(ex, d) = ex isa Symbol ? get(d, ex, ex) :
    ex isa Expr ? Expr(ex.head, (subst(a, d) for a in ex.args)...) : ex
numeric(ex, vals) = Core.eval(Main, subst(ex, Dict{Symbol,Any}(pairs(vals))))
holds(c::GruntzLimit.CaseCondition, vals) = numeric(Expr(:call, c.rel, c.lhs, c.rhs), vals) === true

function matches(r, ans, vals)
    (ans isa Symbol && ans in (:nolimit, :undefined)) && return r === ans
    (r isa GruntzError || r isa Symbol && r in (:nolimit, :undefined)) && return false
    v, w = Float64(numeric(r, vals)), Float64(numeric(ans, vals))
    isinf(w) ? v == w : isapprox(v, w; rtol = 1e-8, atol = 1e-12)
end
show_r(r) = r isa GruntzError ? "not computed: " * r.msg : string(r)

let ndone = 0, n = 0, t0 = time()
    for (i, (f, x0, dir, cases, src)) in enumerate(PROBLEMS)
        println("$i. lim x → $x0 ($dir) of $f   [$src]")
        lc = try
            gruntz_cases(f, :x, x0; dir)
        catch err
            err
        end
        if !(lc isa GruntzLimit.LimitCases)
            println("   error: ", sprint(showerror, lc))
            n += length(cases)
            continue
        end
        for (conds, v) in lc
            println("   → ", isempty(conds) ? "always" : join(string.(conds), " && "), "  ⇒  ", show_r(v))
        end
        for (cond, vals, ans) in cases
            hits = [v for (conds, v) in lc if all(c -> holds(c, vals), conds)]
            ok = length(hits) == 1 && (try matches(hits[1], ans, vals) catch; false end)
            n += 1; ndone += ok
            got = isempty(hits) ? "no case applies" : length(hits) > 1 ? "$(length(hits)) cases apply" : show_r(hits[1])
            println("   ", ok ? "✓" : "✗", " ", rpad(string(cond), 24), " want ", rpad(string(ans), 10), " got ", got)
        end
    end
    println("\n$ndone of $n cases right ($(round(time() - t0; digits = 1)) s)")
end
