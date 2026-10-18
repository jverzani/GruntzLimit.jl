# GruntzLimit.jl

[![Limits, correct of 66: GruntzLimit 66, SymbolicLimits 37](https://img.shields.io/badge/limits%2C%20correct%20of%2066-GruntzLimit%2066%20%C2%B7%20SymbolicLimits%2037-2f8a4c)](https://htmlpreview.github.io/?https://github.com/jverzani/GruntzLimit.jl/blob/main/benchmark/limits/results/limits_comparison.html)

Limits of univariate real expressions using the algorithm of D. Gruntz,
[*On Computing Limits in a Symbolic Manipulation System*](https://doi.org/10.3929/ethz-a-001631582)
(PhD thesis, ETH Zürich, 1996).

The package does not depend on a computer algebra system. Any symbolic term type that
implements the [TermInterface.jl](https://github.com/JuliaSymbolics/TermInterface.jl)
methods `iscall`, `operation` and `arguments` can be used. These docs show three such types:

* [SymEngine.jl](https://github.com/symengine/SymEngine.jl) (`Basic`), a full symbolic
  library whose answers come back as exact `Basic` values;
* [SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl), the term
  library underlying Symbolics.jl;
* Julia's own `Expr`, which needs no extra packages at all.

[SimpleExpressions.jl](https://github.com/jverzani/SimpleExpressions.jl) is also tested.

The input is converted to an internal canonical form. All of the algorithm's work (finding
the most rapidly varying subexpressions, rewriting, series expansion) is done there, and the
answer is rebuilt in your term type by calling operations as functions.

This package was implemented by Claude Code. See also
[SymbolicLimits.jl](https://github.com/SciML/SymbolicLimits.jl), which implements Gruntz's
algorithm for Symbolics.jl.
The [comparison](https://htmlpreview.github.io/?https://github.com/jverzani/GruntzLimit.jl/blob/main/benchmark/limits/results/limits_comparison.html) (the badge above) has
both packages on 66 limit problems, the examples of Gruntz's thesis among them; see
`benchmark/limits/README.md` in the repository to rerun it.

## Example

```@example index
using GruntzLimit
using SymEngine: @vars
@vars x a

gruntz_limit((1 + a/x)^x, x, Inf)
```

```@example index
gruntz_limit((x^x - x^a)/(a^x - a^a), x, a)
```

The same limit with `Expr` input, with the variable and parameter given as `Symbol`s:

```@example index
gruntz_limit(:((x^x - x^a)/(a^x - a^a)), :x, :a)
```

The only entry point is [`gruntz_limit`](@ref). When a limit does not exist, or cannot be
computed, it throws a [`GruntzError`](@ref).
