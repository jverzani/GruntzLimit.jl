# Usage

```julia
gruntz_limit(f, x, x0 = Inf; dir = :+, build = nothing, lift = nothing)
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

`+`, `-`, `*`, `/`, `^`, `inv`, `sqrt`, `cbrt`, `exp`, `log` (one or two arguments), `sin`,
`cos`, `tan`, `atan`, `abs`, `sinh`, `cosh`, `tanh`.

Each operation can be given as a Julia `Function` or as its `Symbol` name. The named constants `pi`/`π`, `E`/`ℯ`,
`EulerGamma`, `Catalan` and `GoldenRatio` are recognised. Anything else gives a
[`GruntzError`](@ref):

```@example expr
try
    gruntz_limit(:(gamma(x)), :x)
catch err
    err
end
```

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
