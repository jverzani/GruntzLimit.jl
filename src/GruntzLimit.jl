"""
    GruntzLimit

Limits of univariate real expressions using Gruntz's algorithm
(D. Gruntz, "On Computing Limits in a Symbolic Manipulation System", 1996).

Expressions are symbolic terms implementing the TermInterface.jl methods `iscall`,
`operation` and `arguments`, with operations that are Julia `Function`s. Tested
targets are SimpleExpressions.jl, SymEngine.jl (`Basic`), SymbolicUtils.jl and
Julia's `Expr`:

    using SimpleExpressions
    @symbolic x
    gruntz_limit(sin(x)/x, x, 0)          # 1
    gruntz_limit(x^2 * exp(-x), x)        # 0
    gruntz_limit(x^2 + 1, x, -Inf)        # Inf

    import SymEngine; SymEngine.@vars y
    gruntz_limit(atan(y)/y, y, 0)         # 1

    gruntz_limit(f, x, x0 = Inf; dir = :+, build = (op, args...) -> op(args...), lift = auto, signs = ())

* `f` is the expression, `x` the symbolic variable (the same object used in `f`).
* `x0` may be `Inf`, `-Inf`, or a finite number / term not containing `x`.
* `dir` is `:+`, `:-` or `:both` (only relevant for finite `x0`).
* `gruntz_cases` (same arguments) gives the limit for each case of the parameters.
* Returns `Inf`, `-Inf`, an `Int`/`Rational`, or a term. Non-rational results are
  rebuilt by *calling the operations as functions* (`+`, `*`, `^`, `exp`, `log`,
  `sin`, `cos`) on the pieces; with a symbolic variable inside that gives a
  symbolic term back. Constant results such as `-π/2` or `exp(1)` stay symbolic
  too: for SimpleExpressions they are built as unevaluated terms (evaluate with
  `r()`), for SymEngine they use `Basic` constants, and for `Expr` input (`x` a
  `Symbol`) results are unevaluated `Expr` calls such as `:(exp(1))`.
  Pass `build` to construct results differently (e.g. `maketerm`-based). `lift`
  converts plain numbers/π into the package's number type; by default it is the
  constructor of `typeof(f)` when that is a non-`Real` `Number` such as `Basic`,
  so a SymEngine limit of exp(1) comes back as `E`, not a float.

Operations understood (given as `Function`s; `Symbol` names are accepted too):
`+ - * / ^ inv sqrt cbrt exp log abs sign floor ceil`, `sin cos tan sec csc cot`, their inverses
`asin acos atan asec acsc acot`, the hyperbolic `sinh cosh tanh sech csch coth` and
their inverses `asinh acosh atanh asech acsch acoth`, `erf erfc` (as defined by
SpecialFunctions.jl), and `gamma loggamma factorial` for an argument that tends to `+∞`
or is constant. Limits that do not
exist because of bounded oscillation (e.g. `sin(x)` at Inf) raise `GruntzError`.

Design: terms are converted to an internal canonical form (sums of monomials with
rational coefficients/exponents over "atoms": variables, exp/log/sin/cos
applications and multi-term bases). That supplies the zero recognition Gruntz's
algorithm needs without depending on a particular CAS.
"""
module GruntzLimit

using TermInterface: iscall, operation, arguments, maketerm
using ScopedValues: ScopedValue, with
import SpecialFunctions

export gruntz_limit, gruntz_cases, GruntzError
# LimitCases and CaseCondition are public types, not exported

const Q = Rational{BigInt}
const HUGE = Q(10)^12   # "exact" precision marker for power series

"""
    GruntzError(msg)

Thrown by [`gruntz_limit`](@ref) when a limit cannot be computed: the limit does not
exist (bounded oscillation such as `sin(x)` at `Inf`, or one-sided limits that differ
with `dir = :both`), the expression uses an unsupported function, or the
algorithm as implemented cannot finish (e.g. the sign of a constant involving a free
parameter cannot be decided).

`kind` is `:nolimit` when the limit is known not to exist, `:undefined` when the
expression is not defined (e.g. `log` of a negative number), `:sign` when the limit
depends on the sign of a constant with a parameter that cannot be decided (give it with
`signs`, or use [`gruntz_cases`](@ref)), and `:fail` otherwise.
"""
struct GruntzError <: Exception
    msg::String
    kind::Symbol
end
GruntzError(msg) = GruntzError(msg, :fail)
Base.showerror(io::IO, e::GruntzError) = print(io, "GruntzError: ", e.msg)

struct NeedMorePrecision <: Exception end
# An infinite limit. The sign is 0 when it depends on a free parameter (e.g.
# a*log(x) as x -> oo): enough to classify exp(a*log(x)) in the mrv set, where only
# finiteness matters. Where the sign itself is needed, `signof` throws `need`, the
# `NeedSign` that left it undecided.
struct Infinity
    sign::Int
    need::Any
end
Infinity(s::Int) = Infinity(s, nothing)
signof(L::Infinity) = L.sign == 0 ? throw(L.need) : L.sign

include("canonical.jl")
include("constructors.jl")
include("numeric.jl")
include("fourier_motzkin.jl")
include("conditions.jl")
include("series.jl")
include("algorithm.jl")
include("oscillation.jl")
include("from_term.jl")
include("to_term.jl")
include("limit.jl")
include("cases.jl")
include("limit_cases.jl")
include("frontend.jl")

end # module
