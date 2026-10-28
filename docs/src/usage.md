# Usage

```julia
gruntz_limit(f, x, x0 = Inf; dir = :+, build = nothing, lift = nothing, signs = ())
gruntz_cases(f, x, x0 = Inf; dir = :+, build = nothing, lift = nothing, signs = ())
```

computes ``\lim_{x \to x_0} f(x)``. The limit point `x0` may be `Inf`, `-Inf`, a number, or an
expression that does not contain `x`. For a finite `x0`, `dir` chooses the side the limit is
taken from: `:+` (from the right, the default), `:-` (from the left), or `:both` (both
one-sided limits are computed and must agree).

Rational limits come back as `Int` or `Rational`, and infinite limits as `Inf` or `-Inf`,
whatever the input type. Other answers, such as ``e`` or ``\pi/2``, are rebuilt in the input's
term type.

## SymEngine

With SymEngine, create the variable (and any parameters) with `@vars`. Then write the
expression as you normally would.

```@example sym
using GruntzLimit
using SymEngine
@vars x a

gruntz_limit(sin(x)/x, x, 0)
```

Limits at infinity are the default:

```@example sym
gruntz_limit(x^2 * exp(-x), x)
```

```@example sym
gruntz_limit(sqrt(x^2 + x) - x, x)
```

Answers that are not rational are returned as exact `Basic` values:

```@example sym
gruntz_limit((1 + 1/x)^x, x)
```

```@example sym
gruntz_limit(atan(x), x, -Inf)
```

```@example sym
gruntz_limit((sin(x)/x)^(1/x^2), x, 0)
```

Parameters can appear in the expression and in the limit point:

```@example sym
gruntz_limit((1 + a/x)^x, x)
```

```@example sym
gruntz_limit((x^x - x^a)/(a^x - a^a), x, a)
```

One-sided limits:

```@example sym
gruntz_limit(1/x, x, 0; dir = :-)
```

```@example sym
gruntz_limit(sqrt(1 - cos(2x))/x, x, 0; dir = :-)
```

Cancellation between exponentials, the kind of limit Gruntz's algorithm handles well:

```@example sym
gruntz_limit(exp(x + exp(-x)) - exp(x), x)
```

```@example sym
gruntz_limit(1/x^2 - 1/sin(x)^2, x, 0)
```

SymEngine's own infinity, `oo`, can be used as the limit point:

```@example sym
gruntz_limit(x^x / exp(x), x, oo)
```

## SymbolicUtils

With [SymbolicUtils.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl), create the
variable (and any parameters) with `@syms`, declaring them `Real`:

```@example su
using GruntzLimit
using SymbolicUtils
using SymbolicUtils: @syms
@syms x::Real a::Real

gruntz_limit(sin(x)/x, x, 0)
```

```@example su
gruntz_limit((x^2 + 1) / (2x^2 - 3), x)
```

Answers that are not rational are built as SymbolicUtils terms with TermInterface's
`maketerm`, so constants stay exact rather than becoming floating point numbers:

```@example su
gruntz_limit((1 + 1/x)^x, x)
```

```@example su
gruntz_limit(atan(1/x), x, 0; dir = :-)
```

```@example su
gruntz_limit(sqrt(1 - cos(2x))/x, x, 0; dir = :+)
```

Parameters may appear in the expression and in the limit point:

```@example su
gruntz_limit((1 + a/x)^x, x)
```

```@example su
gruntz_limit(sqrt(x^2 + a*x) - x, x)
```

```@example su
gruntz_limit((x^x - x^a)/(a^x - a^a), x, a)
```

A symbolic answer can be evaluated with SymbolicUtils' `substitute`:

```@example su
L = gruntz_limit((sin(x)/x)^(1/x^2), x, 0)
```

```@example su
SymbolicUtils.substitute(L, Dict(); fold = Val(true))
```

### Constants in SymbolicUtils input

SymbolicUtils turns some constants into floating point numbers when an expression is built.
`π*x` keeps `π` exact, but `atan(x) - π/2` becomes `atan(x) - 1.5707963267948966`. The limit
is then taken for that floating point number, which changes the answer:

```@example su
gruntz_limit(x * (atan(x) - π/2), x)       # exact answer: -1
```

To keep `π` exact in such an expression, build it the way SymbolicUtils represents it in
`π*x`:

```@example su
PI = SymbolicUtils.maketerm(typeof(x), identity, Any[π], nothing)
gruntz_limit(x * (atan(x) - PI/2), x)
```

## Julia `Expr`

TermInterface.jl defines `iscall`, `operation` and `arguments` for Julia's `Expr`, so a quoted
expression works without any symbolic package. The variable is passed as a `Symbol`:

```@example expr
using GruntzLimit

gruntz_limit(:(sin(x)/x), :x, 0)
```

```@example expr
gruntz_limit(:(1/x^2 - 1/sin(x)^2), :x, 0)
```

```@example expr
gruntz_limit(:(x/abs(x)), :x, 0; dir = :-)
```

```@example expr
gruntz_limit(:(floor(x)), :x, 2; dir = :-)
```

A parameter is just another `Symbol`, and it can also be the limit point:

```@example expr
gruntz_limit(:((x^x - x^a)/(a^x - a^a)), :x, :a)
```

### `Expr` answers

For `Expr` input, a non-rational answer is returned as an unevaluated `Expr`, so it stays exact
and may contain parameters:

```@example expr
gruntz_limit(:((1 + 1/x)^x), :x)
```

```@example expr
gruntz_limit(:((1 + a/x)^x), :x)
```

```@example expr
gruntz_limit(:(sqrt(x^2 + a*x) - x), :x)
```

```@example expr
L = gruntz_limit(:(atan(1/x)), :x, 0; dir = :-)
```

The result is an ordinary expression, so it can be evaluated:

```@example expr
eval(L)
```

The answer is assembled by a `build` function, which receives an operation (a Julia
`Function` such as `+`, `*`, `^`, `exp`, `log`, `sin`, `cos`, `atan`, `sqrt`) and its
arguments. For `Expr` input the default is `(op, args...) -> Expr(:call, nameof(op), args...)`.
Pass a different `build` to change this. For example, calling the operations evaluates
constant answers to floating point:

```@example expr
gruntz_limit(:((1 + 1/x)^x), :x; build = (op, args...) -> op(args...))
```

## Supported functions

The operations understood are

* arithmetic: `+`, `-`, `*`, `/`, `^`, `inv`, `sqrt`, `cbrt`, `abs`, `sign`;
* `floor` and `ceil`, when their argument has a finite limit;
* `exp`, and `log` (one or two arguments);
* trigonometric: `sin`, `cos`, `tan`, `sec`, `csc`, `cot`;
* inverse trigonometric: `asin`, `acos`, `atan`, `asec`, `acsc`, `acot`;
* hyperbolic: `sinh`, `cosh`, `tanh`, `sech`, `csch`, `coth`;
* inverse hyperbolic: `asinh`, `acosh`, `atanh`, `asech`, `acsch`, `acoth`;
* the error function `erf` and `erfc`, as in SpecialFunctions.jl.

Inside the package, most of these are rewritten in terms of `sin`, `cos`, `atan`, `erf`, `exp` and `log`.
An answer involving them is correct, but it may be written differently from the input.
For example, ``\arcsin(1/2)`` comes back in terms of `atan`:

```@example expr
L = gruntz_limit(:(asin(x)), :x, 1//2)
```

```@example expr
eval(L) ≈ π/6
```

SymEngine simplifies the same answer when it is rebuilt:

```@example sym
gruntz_limit(asin(x), x, 1//2)
```

Each operation can be given as a Julia `Function` or as its `Symbol` name. The named constants `pi`/`π`, `E`/`ℯ`,
`EulerGamma`, `Catalan` and `GoldenRatio` are recognised. In an `Expr`, the bare symbols
`pi`, `π` and `ℯ` are treated as these constants, not as parameters:

```@example expr
gruntz_limit(:(x * (atan(x) - pi/2)), :x)
```

Anything else gives a
[`GruntzError`](@ref):

```@example expr
try
    gruntz_limit(:(gamma(x)), :x)
catch err
    err
end
```

## Parameters and cases

A parameter is taken to be a real number of unknown sign. `gruntz_limit` answers when the
limit does not depend on the sign, as for

```@example expr
gruntz_limit(:(x^a / exp(x)), :x)
```

which is 0 whatever `a` is. When the limit depends on the sign of a constant, a
[`GruntzError`](@ref) names the constant:

```@example expr
try
    gruntz_limit(:(x^(a - 2)), :x)
catch err
    err
end
```

### A limit for each case

[`gruntz_cases`](@ref) computes the limit for each case of the parameters. When the limit
depends on the sign of a constant such as `a - 2`, it is computed for `a < 2`, `a == 2`
and `a > 2`. The case `a == 2` is computed by substituting `a = 2`. Cases with the same
limit are merged:

```@example expr
gruntz_cases(:(x^(a - 2)), :x)
```

```@example expr
gruntz_cases(:(x^a * log(x)), :x, 0)
```

A limit can be `:undefined` for some parameters (`a^x` needs `a > 0`), or `:nolimit`
(the one-sided limits differ):

```@example expr
gruntz_cases(:(a^x), :x)
```

```@example expr
gruntz_cases(:(1/(x - a)), :x, 0; dir = :both)
```

`gruntz_limit` takes a constant that it cannot decide to be nonzero, and so gives the
generic answer `a/b` here. `gruntz_cases` also gives the cases `b == 0`:

```@example expr
gruntz_limit(:((a*x^2 + x)/(b*x^2 + 1)), :x)
```

```@example expr
gruntz_cases(:((a*x^2 + x)/(b*x^2 + 1)), :x)
```

The result is a [`GruntzLimit.LimitCases`](@ref), a vector of `conditions => limit` pairs.
Each condition is a [`GruntzLimit.CaseCondition`](@ref), with terms of the input's type:

```@example expr
cs = gruntz_cases(:(sqrt(x^2 + a*x) - b*x), :x)
[(string.(conds), v) for (conds, v) in cs]
```

A `LimitCases` is a vector, so `cs[1]`, `cs[end]` and `filter` work. Calling it with
values of the parameters gives the limit for those values. The values are given as pairs
`parameter => value` (or a `Dict`), with the parameters written as in `signs` below.
Indexing with them gives the case, `conditions => limit`:

```@example expr
cs = gruntz_cases(:((a^x + b^x)^(1/x)), :x)
cs(:a => 2, :b => 3), cs(:a => -1, :b => 2)
```

```@example expr
cs[:a => 2, :b => 3]
```

A condition is shown solved for a parameter when it is linear in one. A case whose
condition `c == 0` cannot be solved for a parameter (`a*b == 1`, say) is not computed. The
case's limit is then a `GruntzError`. Merging is pairwise, so a union of several cases may
be listed in parts.

### Giving signs

TermInterface has no way to state assumptions, so signs are given with the `signs` keyword,
to `gruntz_limit` or `gruntz_cases`. They are pairs `c => s`. Here `c` is a parameter or an
expression in the parameters. `s` is one of `:positive`, `:negative`, `:nonnegative`,
`:nonpositive`, `:nonzero` or `:zero`. For `:zero`, the equation `c = 0` is solved for a
parameter, which is substituted:

```@example expr
gruntz_limit(:(x^a), :x; signs = Dict(:a => :positive))
```

```@example expr
gruntz_limit(:(x^(a - 2)), :x; signs = Dict(:(a - 2) => :negative))
```

```@example expr
gruntz_cases(:(x^a / (1 + x^b)), :x; signs = Dict(:b => :positive))
```

```@example expr
gruntz_cases(:(x^a), :x; signs = Dict(:a => :nonnegative))
```

Write the keys the way `f` is written: `Symbol`s and `Expr`s for an `Expr`, and terms of
the same package otherwise:

```@example sym
@vars b
gruntz_limit(exp(a*b*x), x; signs = Dict(a => :positive, b => :negative))
```

```@example sym
gruntz_limit(x^(a - 2), x; signs = Dict(a - 2 => :negative))
```

Signs that follow from those given are used. Linear consequences (`a > 2` from `a - 2 > 0`)
are found by Fourier–Motzkin elimination. Products, quotients, powers and logarithms of
parameters take their signs from their factors (`log(a)` has the sign of `a - 1`).

Signs that leave a logarithm or a fractional power of the parameters without a valid
argument (`log(a*x)` or `sqrt(a)` with `a` negative) make the limit undefined: a
`GruntzError` of kind `:undefined`. Without such signs, `gruntz_limit` takes the
parameters to be values for which `f` is defined, as it takes them to be nonzero.

## When there is no limit

A [`GruntzError`](@ref) is also thrown when the limit does not exist. For example, bounded
oscillation:

```@example sym
try
    gruntz_limit(sin(x), x)
catch err
    err
end
```

or one-sided limits that disagree, with `dir = :both`:

```@example sym
try
    gruntz_limit(x/abs(x), x, 0; dir = :both)
catch err
    err
end
```
