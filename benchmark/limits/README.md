# Limits comparison

GruntzLimit on three term types, and SciML's
[SymbolicLimits.jl](https://github.com/SciML/SymbolicLimits.jl) on
SymbolicUtils terms, on the limit problems of `problems.jl`:

| Method | Package | Terms |
|---|---|---|
| `expr` | GruntzLimit (this package) | Julia `Expr` |
| `symengine` | GruntzLimit | SymEngine |
| `symbolicutils` | GruntzLimit | SymbolicUtils |
| `symboliclimits` | SymbolicLimits, `limit` | SymbolicUtils |
| `symboliclimits_explog` | SymbolicLimits, `limit`, after rewriting powers and radicals as `exp`/`log` | SymbolicUtils |

The result is a page, `results/limits_comparison.html`, with a summary
(counts and times) and a grid with one row per method, one column per
problem. Selecting a problem shows the limit and each method's answer.

## The problems

`problems.jl` has 66 limits, each `(f, x0, dir, answer, source)`:

- the 22 worked examples of §8 of Gruntz's thesis (D. Gruntz, *On Computing
  Limits in a Symbolic Manipulation System*, ETH Zürich, 1996), plus the
  example of SymbolicLimits' README: nested exponentials and logarithms
  that cancel in ways numerical evaluation cannot follow;
- limits at ±∞ such as `x((1 + 1/x)^x − ℯ)`, `log(x)^log(x)/x^log(log(x))`
  (identically 1) and nested radicals;
- limits at finite points needing high-order series, such as
  `(sin(tan x) − tan(sin x))/x⁷` at 0 (−1/30), one-sided limits, and limit
  points π/4 and π/2;
- limits with parameters `a` and `b`, at ∞, at 0, and at the point `a`.

Answers are Julia expressions in `a` and `b`; the parameters are taken to be
positive (`a = 1.7`, `b = 2.3` in the check).

## Running it

GruntzLimit comes from this checkout; everything else from the registry.

```sh
cd benchmark/limits
julia --project=env_gruntz -e 'using Pkg; Pkg.instantiate()'   # once, or after changing a package
julia --project=env_sl -e 'using Pkg; Pkg.instantiate()'
julia run_all.jl            # or `julia run_all.jl 120` for a 120 s limit per problem
```

`run_all.jl` runs the methods one after another, so they do not compete for
the CPU, and then builds the page. Open `results/limits_comparison.html` in a
browser; it is self-contained.

To run or rerun one method, then rebuild the page:

```sh
julia supervise.jl symengine env_gruntz 60
julia build.jl
```

To pick up a newer registered SymbolicLimits, run
`julia --project=env_sl -e 'using Pkg; Pkg.update()'` first.

## How it works

| File | Role |
|---|---|
| `problems.jl` | the problems, as quoted expressions |
| `worker_*.jl` | one per method: loads the packages, makes the variables, and defines `LIMIT`, `SOLVED` and `EVAL` |
| `su_common.jl` | the SymbolicUtils variables, constants and evaluation, shared by the GruntzLimit and SymbolicLimits workers so both get the same terms |
| `sl_common.jl` | the call to SymbolicLimits, shared by its two workers |
| `core.jl` | shared by the workers: builds each problem with the worker's variables, takes the limit, checks it, writes a line per problem |
| `supervise.jl` | runs a worker; if one problem takes longer than the limit, kills the process, records a timeout and restarts at the next problem |
| `build.jl`, `template.html` | turn the results into the page |
| `env_gruntz`, `env_sl` | the environments: GruntzLimit with SymEngine and SymbolicUtils; SymbolicLimits with SymbolicUtils |

Each problem is built from its expression with the worker's own values for
`x`, `a`, `b`, `π` and `ℯ`: `SymEngine.@vars` with `PI` and `E`; SymbolicUtils
`@syms x::Real a::Real b::Real` with `identity(π)` and `exp(Const(1))` (as in
`test/test_SymbolicUtils.jl`). For `expr` the quoted expression is the term.
The direction is given to both packages: GruntzLimit's `dir = :+`, `:-`,
`:both`, SymbolicLimits' `:right`, `:left`, `:both` (none at ±∞).

SymbolicLimits supports only `+`, `*`, integer powers, `exp` and `log`. The
`symboliclimits_explog` worker rewrites `sqrt(u)`, `cbrt(u)` and `u^v` (v not an
integer) as `exp(log(u)/2)`, `exp(log(u)/3)` and `exp(v*log(u))` first, to show
what its algorithm does with the rest. Trigonometric functions are left as they are.

What is recorded:

- **Answer**: the method returned a value free of `x` and threw nothing.
  GruntzLimit throws `GruntzError` when it can not compute a limit.
- **Correct**: the answer, with `a = 1.7` and `b = 2.3`, evaluates to the known
  limit to a relative 1e-8; an infinite limit must match exactly.
- **Not checked**: an answer that could not be evaluated to a number.
- **Wrong**: an answer with a different value (or a non-finite value where the
  limit is finite).
- **Times**: each method starts cold in a new process. Solving time is the sum
  of the per-problem times, so it includes compiling; load time is loading the
  packages; wall time is everything, restarts included. Compare times only
  within one run.

SymbolicLimits' assumptions (other than `true`) are appended to its answer.

`results/results_NAME.tsv` has one line per event, tab separated:

| Line | Fields |
|---|---|
| `L` | load time in seconds, first problem of this process (one line per process start) |
| `V` | package name, version (first process only) |
| `S` | problem, start time (used by `supervise.jl` to enforce the limit) |
| `R` | problem, status (`solved`, `unsolved`, `error`, `timeout`, `crash`), check (`verified`, `unverified`, `wrong`, `none`), seconds, the answer or error (first 400 characters) |
| `D` | the worker finished |
| `T` | wall time in seconds, limit in seconds |

`results/commits.tsv` records the git commit of GruntzLimit (and whether it
had uncommitted changes) when `run_all.jl` ran.

## Adding a method

Write `worker_NAME.jl` following the others. Before `include("core.jl")` it
must set `T_START`, load the packages, and define

- `VAR::Dict{Symbol,Any}`: the values of `x a b π ℯ`
- `LIMIT(f, x, x0, dir)`: the method; `x0` is `±Inf` or a built term, `dir` is `:+`, `:-` or `:both`
- `SOLVED(out)::Bool`: did it return a limit?
- `EVAL(out, vals)`: the value of `out` with each parameter `v` replaced by
  the number `vals[v]`, or `nothing` if it does not evaluate to a number
- optionally `BUILD(ex)`, the term from the problem's expression (by default,
  the expression evaluated with the values of `VAR`), and `NOTE()`, a string
  appended to the recorded answer

Then add it to the loop in `run_all.jl` and to `METHODS` in `build.jl`.

## Updating the page

`build.jl` fills in the numbers, grid, times and versions. The "What stands
out" section is written by hand in `template.html`; check it against the new
results and edit it before publishing.

The package README and the docs' home page (`docs/src/index.md`) have a
badge comparing the number of problems solved
correctly by `symbolicutils` (GruntzLimit, SymbolicUtils) and `symboliclimits`
(SymbolicLimits, the same terms). It links to the page through
htmlpreview.github.io, from `main`, so the page must be committed and pushed
there. It is a static badge: after a run that changes these numbers, update
them in the badge URL and its alt text, in both places.

## Results so far

Correct out of 66. Times are on one machine and only comparable within a run.

| Date | Julia | GruntzLimit | expr | symengine | symbolicutils | symboliclimits | symboliclimits_explog |
|---|---|---|---|---|---|---|---|
| 2026-10-17 | 1.13.0 | `d64dfcd` | 60 | 61 | 61 | 19 | 37 |
| 2026-10-17 | 1.13.0 | `d64dfcd` + fixes | 65 | 65 | 65 | 19 | 37 |
| 2026-10-17 | 1.13.0 | `d64dfcd` + fixes, parameter signs | 66 | 66 | 66 | 19 | 37 |

Notes:

- The second run is after GruntzLimit learned sin and cos at rational
  multiples of π (it had answered problems 56 and 57 wrongly, not recognising
  `cos(π/2)` as zero), irrational ratios of exponents (5, 12) and `//` in
  `Expr` input (15). The SymbolicLimits rows were not rerun.
- The third run is after GruntzLimit stopped asking for the sign of a
  parameter where only finiteness matters, which solves xᵃ/eˣ (38).
- SymbolicLimits 1.2.2 returns ∞ for Gruntz 8.18 (limit 2), and returns the
  assumption `false` with several correct answers.
