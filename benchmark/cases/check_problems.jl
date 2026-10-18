# julia check_problems.jl
# Checks the reference answers of problems.jl numerically: for each case, f is
# evaluated in BigFloat at points approaching x0, with the parameters set to the
# case's sample values. Also checks that each sample satisfies its own condition
# and no other condition of the problem (the cases do not overlap).
setprecision(4000)
const PROBLEMS = include(joinpath(@__DIR__, "problems.jl"))

function evalwith(ex, vals; x = nothing)
    m = Module()
    for (k, v) in pairs(vals)
        Core.eval(m, :($k = $(v isa Integer ? v : big(v))))
    end
    x === nothing || Core.eval(m, :(x = $x))
    Core.eval(m, ex)
end

value(f, vals, p) = try
    v = evalwith(f, vals; x = p)
    v isa Real && isfinite(v) ? BigFloat(v) : big(NaN)   # complex (or 1/0): not defined
catch err
    err isa DomainError || err isa DivideError || rethrow()
    big(NaN)
end

# the values of f along points approaching x0 from the side s (+1 or -1). At ±Inf
# the points are not integers (where a^x is real for a < 0) and at most 10^8, as
# 3^(10^16) overflows even BigFloat.
function approach(f, vals, x0, s)
    if x0 isa Real && isinf(x0)
        [value(f, vals, sign(x0) * (big(10)^k + big(1) / 3)) for k in (4, 6, 8)]
    else
        p = BigFloat(evalwith(x0, vals))
        [value(f, vals, p + s * big(10.0)^(-k)) for k in (8, 16, 32)]
    end
end

function check_side(vs, ans, vals)
    any(isnan, vs) && return ans === :undefined
    ans === :undefined && return false
    ans === :nolimit && return maximum(vs) - minimum(vs) > 0.1 * max(1, minimum(abs, vs))
    r = BigFloat(evalwith(ans, vals))
    if isinf(r)
        # growing in magnitude, at least tenfold (x^(1/2) is only 10^4 at x = 10^8)
        return all(v -> sign(v) == sign(r), vs) && issorted(abs.(vs)) && abs(vs[end]) > 10 * abs(vs[1])
    end
    errs = abs.(vs .- r)
    errs[end] <= 1e-2 * max(1, abs(r)) && errs[end] <= errs[1] + 1e-30
end

function check(f, x0, dir, ans, vals)
    sides = x0 isa Real && isinf(x0) ? [1] : dir === :+ ? [1] : dir === :- ? [-1] : [1, -1]
    vs = [approach(f, vals, x0, s) for s in sides]
    if ans === :nolimit && length(sides) == 2 && !any(v -> any(isnan, v), vs)
        # a two-sided limit fails when the sides tend to different values
        return check_side(vs[1], :nolimit, vals) || abs(vs[1][end] - vs[2][end]) > 0.1 ||
               sign(vs[1][end]) != sign(vs[2][end])
    end
    all(v -> check_side(v, ans, vals), vs)
end

let bad = 0
    for (i, (f, x0, dir, cases, src)) in enumerate(PROBLEMS)
        for (j, (cond, vals, ans)) in enumerate(cases)
            ok = check(f, x0, dir, ans, vals)
            own = evalwith(cond, vals) === true
            others = [k for (k, (c, _, _)) in enumerate(cases) if k != j && evalwith(c, vals) === true]
            if !(ok && own && isempty(others))
                bad += 1
                println("problem $i ($src), case $cond: ",
                        ok ? "" : "answer $ans not confirmed; ",
                        own ? "" : "sample $vals fails its condition; ",
                        isempty(others) ? "" : "sample also satisfies cases $others")
            end
        end
    end
    n = sum(length(p[4]) for p in PROBLEMS)
    println(bad == 0 ? "all $n cases of $(length(PROBLEMS)) problems confirmed" : "$bad of $n cases not confirmed")
end
