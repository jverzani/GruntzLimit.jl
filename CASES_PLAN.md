# Limits that depend on cases of a parameter

Notes for the `cases` branch: what happens now, what the test problems show, and a
sketch of how GruntzLimit could return a limit for each case of the parameters.

## The goal

`lim_{x→∞} x^(a−2)` is 0, 1 or ∞ as `a < 2`, `a = 2` or `a > 2`. GruntzLimit should be
able to say so, rather than throw or quietly assume one case.

## Status (2026-10-18)

Steps 1–6 of the suggested order below are implemented on this branch:

- `gruntz_cases(f, x, x0; ...)` returns a `LimitCases`, a vector of
  `Vector{CaseCondition} => limit`. A limit is a value, `:nolimit`, `:undefined`, or a
  `GruntzError` for a case not computed. `benchmark/cases/cases.jl` scores it at
  **63 of 65 cases**; the two misses are problem 17 (out of scope).
- `gruntz_limit` throws a `GruntzError` naming the constant whose sign is needed
  (`the limit depends on the sign of `a - 2``). `signs` takes constants as keys and 0 as a
  sign (`Dict(:(a - 2) => :negative)`, `Dict(:b => :zero)`).
- `GruntzError` has a `kind`: `:nolimit`, `:undefined` or `:fail`.

How it works (src/conditions.jl and src/cases.jl):

- A context `CTX` of conditions `c > 0`, `c < 0`, `c == 0`, `c != 0` on constants, each
  normalised (first non-constant monomial with coefficient 1). `possible_signs(s)` gives the
  signs the context allows. It uses Fourier–Motzkin elimination over the parameter
  monomials, numeric factors evaluated, plus sign facts for products and functions of
  parameters (`log(s)` has the sign of `s - 1`). Known-sign factors and denominators are
  cleared first (`a/b - 1` → `a - b`). Results are cached for each context.
- `csign` throws `NeedSign(c, possible, zerotest)` when undecided. In `gruntz_cases` mode
  (`CASES`), zero tests do the same. The zero tests are in the leading coefficient
  (`numzero`, `dropzeros` in `split_lead`), in `compare`, and in a positivity check in
  `mklog`, which makes `a^x` `:undefined` for `a <= 0`.
- `solve_cases` reruns the limit for each possible sign of `split_target(c)`, which splits a
  product one factor at a time and `log(s)` on `s - 1`. The case `c == 0` is solved for a
  parameter (`solve_zero`: linear, `log(p)`, or `p^n`) and substituted at conversion
  (`SUBST`, through `leafS`). The tree is simplified (`c < 0`, `c > 0` alike → `c != 0`; a
  zero case merged into a neighbour, also after substitution). It is then flattened and
  merged pairwise (`merge_cases`: the union described by at most 3 of the cases' conditions;
  implied conditions pruned).
- Series precision is a set of bounds (`Prec`). A term is kept only when it is decidably below
  all of them, so precision comparisons never ask for a split.
- When moving up, mrv members that no longer occur are dropped (x of log(x)). Otherwise
  `w = exp(-x)` made every term a parameter power `w^(-a)`. This was the "spurious dependence"
  of problem 12.

Known weaknesses:

- Merging is pairwise, so `max(a, b)` (problem 11) is correct but listed in 9 cases.
- FM treats `log(a)` and `a` as unrelated, so a condition such as `a <= b` held as
  `log(b) - log(a) >= 0` does not prune `b > 1` given `a > 1`.
- A zero case that cannot be solved for a parameter (`a*b == 1`) is "not computed".
- `gruntz_limit` still assumes undecided constants are nonzero (generic answers).
- Square roots of parameters are not checked for `>= 0` (only `log` is).

## Before this work

- A free parameter is taken to be nonzero, of unknown sign.
- When the algorithm needs the sign of a constant containing a parameter, it throws
  `GruntzError("cannot decide the sign of an expression containing the free symbol `a`")`.
- The experimental `signs` keyword (`signs = Dict(a => 1)`) gives parameters' signs. A
  constant's sign is inferred only when all its terms have the same sign, so `2a + b` is
  decided for a, b > 0, but `a − 2` is not.
- Where only the size of a limit matters (deciding that `x^a` and `x` are comparable), the
  sign is not needed: `Infinity(0, why)`, thrown by `signof` where the sign is used.

## The test problems

`benchmark/cases/problems.jl` has 19 problems with 65 cases. Each case is a condition, a
sample value of the parameters inside it, and the answer (a value, `:nolimit` or
`:undefined`). The conditions of a problem cover all real values of the parameters, so a
case-splitting method can be checked for completeness as well as for each answer.
`check_problems.jl` confirms every answer numerically (BigFloat, at points approaching the
limit point, with the sample values), and that no sample satisfies another case's condition.

`baseline.jl` runs today's GruntzLimit (`Expr` input). Without information, no problem gets
its cases. With `signs` from each case's sample (and a parameter whose sample is 0
substituted), **40 of 65 cases** come out right.

## What the baseline shows

1. **Signs of constants that are not a single parameter.** Problems 2, 6, 7, 10, 11 and 13
   need the sign of `a − 2`, `a − b`, `1 − b` or `log(a)`. With numbers in place of the
   parameters they all work, so this is what case splitting has to supply.

2. **Generic answers returned silently.** Problems 14, 15 and 19 return `a/b`, `a/b` and
   `−1/a` with no information, correct only for `b ≠ 0` or `a ≠ 0`. The cause is that a
   leading series coefficient such as `b` is taken to be nonzero: `numzero` returns false
   when the constant can not be evaluated. A case-splitting version must make this an
   explicit condition (`b ≠ 0`), and treat `b = 0` as a branch of its own.

3. **Dependence that is not in the answer.** Problem 12, `(x^a + 1)^(1/log x)`, fails even
   with the sign of `a` given. The sign is asked for by `value(::Ex)` in `polyPS`, which
   computes how many series terms are needed from the valuation, here `|a|`. The answer
   (1 for a ≤ 0, `exp(a)` for a > 0) does not depend on it. Splitting there gives branches
   with equal answers, to be merged; better, `polyPS` should not need the numerical value.

4. **`:undefined` passes by accident.** For `a^x` and `(a^x + b^x)^(1/x)` with a ≤ 0, the
   baseline throws, so the case is counted as done, but the error is about the sign of `a`,
   not about `a^x` being undefined. `mklog` of a constant rejects only negative *rational*
   constants. `log(a)` with a ≤ 0 needs its own branch: "undefined".

5. **Out of scope.** Problem 17, `x^a · sin(1/x)` at 0⁺, fails for every a, even with a
   number substituted: Gruntz's algorithm cannot bound an oscillating factor. That needs a
   squeeze argument, not case splitting.

## Where the algorithm needs a sign or a zero test (src/)

| Place | Question | Today, with a parameter |
|---|---|---|
| `csign` | sign of a constant | `infer_sign` from `signs`, else the free-symbol error |
| `limitinf` (e0 < 0) | sign of the leading coefficient | `Infinity(0, why)` |
| `signof` | sign of an infinite limit | throws `why` |
| `Ex` `isless`, `sign` | order of two exponents of w | `csign` of their difference |
| `value(::Ex)` in `polyPS` | number of terms to compute | numerical value: the free-symbol error |
| `leadterm` / `numzero` | is a coefficient zero? | *assumed nonzero* |
| `compare` | is the ratio of logs zero? | `iszero` of the Sum: *nonzero assumed* |
| `mklog` of a constant | is it positive? | checked for rational constants only |

The two rows marked *assumed* are where answers are silently generic.

## A sketch

**Conditions.** A condition is a constant `c` (a `Sum` free of `x`) with a sign: `c > 0`,
`c = 0` or `c < 0` (and `c ≠ 0` for a zero test). A *context* is a list of conditions.
`csign` consults the context first: an exact match of the `Sum` (by `skey`), then inference
from the signs it knows, like `infer_sign` but with known `Sum`s as well as parameters.

**Branching.** Make the free-symbol error an internal exception carrying the constant,
`NeedSign(c)`, instead of matching a `GruntzError` message. A driver runs the limit under a
context. On `NeedSign(c)` it reruns the limit three times, adding `c < 0`, `c = 0` and
`c > 0` to the context. Rerunning from the start is simple, and the depth is small in practice.
A zero test (`numzero`) raises `NeedNonzero(c)` and splits in two.

**The zero branch.** "c = 0" can not just be recorded: the series must then treat `c` as zero.
When `c` is linear in one parameter (`a − 2`, `b`), solve for it and substitute into `f`, `x0`
and the context; otherwise mark the branch "not computed".

**Pruning.** Contexts can be contradictory (`a < 0` and `a − 2 > 0`). For conditions linear in
the parameters, check feasibility (Fourier–Motzkin is enough for two or three parameters).
Otherwise keep the branch; sampling could flag likely contradictions.

**Merging.** Branches with equal answers are merged (`a < 0` or `a = 0` becomes `a ≤ 0`).
Merging needs `lim_equal` on answers and a little condition simplification, for display.

**Return type.** Something like

```julia
struct LimitCases
    cases::Vector{Pair{Vector{Condition}, Any}}   # conditions => limit, :nolimit or :undefined
end
```

The conditions are rebuilt with the user's `build`: `:(a - 2 > 0)` for `Expr`; for SymEngine
or SymbolicUtils a term with a relation. It could be opt-in, `gruntz_limit(...; cases = true)`
or a new function, so that `gruntz_limit` keeps returning one value. Without opt-in, a needed
split would throw an error naming the condition (rebuilt with `build`, not as an internal key).

**`signs`.** It becomes the starting context. It could accept constants as keys too
(`Dict(:(a - 2) => :positive)`), which is useful on its own.

## Suggested order

1. Replace the message matching with an internal `NeedSign(c)` exception, and make the
   error name the constant (`the sign of a - 2 is needed`). Useful at once, and the hook
   the rest needs.
2. A context of conditions on constants, so `signs` can take `a - 2 => :positive`.
3. Make the zero tests explicit (`numzero`, `compare`), so generic answers are no longer
   silent: at least an error, or `b ≠ 0` noted.
4. Remove the spurious dependence in `polyPS` (problem 12).
5. The driver: branching, the zero branch by substitution, pruning, merging, the return type.
6. A harness in `benchmark/cases` that scores a method per case, like `benchmark/limits`.

## Open questions

- Is a return type worth it, or are errors that name the condition, plus `signs` with
  constants as keys, enough in practice?
- How should conditions be shown for each term type (SymEngine has no relations)?
- Should "not computed" branches (a zero condition that can not be solved for) be returned,
  or should the call fail?
- Parameters are assumed nonzero today. In a case-splitting mode, should `a = 0` become a
  branch wherever that assumption is used (`compare`, the mrv classification)?
