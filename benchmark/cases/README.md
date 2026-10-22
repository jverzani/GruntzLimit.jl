# Limits with cases

Limits whose value depends on the parameters `a` and `b`, for work on returning a limit
for each case of the parameters. The design notes are in `CASES_PLAN.md` at the top of
the repository.

| File | Role |
|---|---|
| `problems.jl` | 27 problems, 86 cases: each `(f, x0, dir, cases, source)`, a case being `(condition, sample, answer)` |
| `check_problems.jl` | confirms every answer numerically, and that the cases do not overlap |
| `cases.jl` | scores `gruntz_cases`: the sample of each case must fall in exactly one returned case, with the right limit |
| `baseline.jl` | `gruntz_limit` without case splitting: with no information, and with `signs` from each case's sample |

```sh
cd benchmark/cases
julia check_problems.jl                              # all 86 cases of 27 problems confirmed
julia --project=../limits/env_gruntz cases.jl        # 84 of 86 cases right (about 14 s)
julia --project=../limits/env_gruntz baseline.jl     # 59 of 86 cases done with signs
```

The two cases `gruntz_cases` misses are those of problem 17, `x^a sin(1/x)` at 0⁺: Gruntz's
algorithm cannot bound an oscillating factor, whatever `a` is.

An answer is a number, `±Inf`, an expression in the parameters, `:nolimit` (the limit does
not exist) or `:undefined` (f is not defined near the limit point for those parameters). The
conditions of a problem cover every real value of the parameters.

`check_problems.jl` evaluates in BigFloat at points approaching the limit point (at ±Inf, the
non-integer points 10⁴ + 1/3, 10⁶ + 1/3, 10⁸ + 1/3; at a finite point, distances 10⁻⁸, 10⁻¹⁶,
10⁻³²). A finite answer must be approached; an infinite one must grow at least tenfold with the
right sign; `:nolimit` must oscillate or differ between the sides; `:undefined` must fail to
evaluate to a finite real number. Changing an answer makes it fail.
