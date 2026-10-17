# How it works

This is an outline of Gruntz's algorithm as implemented here. Gruntz's thesis has the
details and proofs.

## Reduction to ``x \to \infty``

Every limit is reduced to a limit at ``+\infty``:

* ``x \to -\infty``: substitute ``x \mapsto -x``;
* ``x \to x_0^+``: substitute ``x \mapsto x_0 + 1/x``;
* ``x \to x_0^-``: substitute ``x \mapsto x_0 - 1/x``;
* `dir = :both` computes both one-sided limits and checks that they agree.

As ``x \to \infty``, each expression handled here eventually has a constant sign. So `abs(u)` is replaced
by `sign(u) * u` before the limit is computed.

## Canonical form

The input term is converted into an internal canonical form: sums of monomials with exact
rational coefficients and exponents, built over *atoms*. An atom is a variable or constant, an
application of `exp`, `log`, `sin`, `cos`, `atan` or `abs`, or a sum used as a base. Some
simplifications are applied during conversion:

* `exp(a + c*log(y))` becomes `y^c * exp(a)`, and `log` of a product splits into a sum;
* `tan`, `sec`, `csc`, `cot` and the hyperbolic functions are rewritten in terms of `sin`,
  `cos` and `exp`;
* the inverse trigonometric functions are rewritten in terms of `atan` (for example
  ``\arcsin u = \arctan\big(u/\sqrt{1-u^2}\big)``), and the inverse hyperbolic functions in
  terms of `log` (for example ``\operatorname{arsinh} u = \log\big(u + \sqrt{u^2+1}\big)``);
* integer powers of short sums are expanded.

These rules give the algorithm the zero recognition it needs, without a full computer
algebra system.

## The most rapidly varying subexpressions

For two functions ``f, g \to \infty``, ``f`` grows faster than ``g`` when
``\log f / \log g \to \infty``. They are in the same *comparability class* when the ratio
tends to a finite nonzero constant. The set ``\Omega`` of most rapidly varying subexpressions of
``f`` is computed recursively. This step itself requires limits, which are computed with the
same algorithm.

If ``x \in \Omega``, the expression is first *moved up* (``x \mapsto e^x``) so that every member of
``\Omega`` is an exponential ``e^{g_i}``.

## Rewriting and series expansion

One member ``e^{g_1}`` of ``\Omega`` is chosen, and ``w = e^{\mp g_1} \to 0^+``. Every
``e^{g_i} \in \Omega`` is rewritten as ``w^{-c_i}\, e^{g_i - c_i g_1}``, where
``c_i = \lim g_i / g_1`` is rational. The expression becomes a function of ``w`` whose
coefficients are less rapidly varying than ``w``. It is expanded as a generalized power series
in ``w``, and the leading term ``c_0 w^{e_0}`` gives the limit:

* ``e_0 > 0``: the limit is ``0``;
* ``e_0 < 0``: the limit is ``\pm\infty``, according to the sign of ``c_0``;
* ``e_0 = 0``: the limit is the limit of ``c_0``, computed recursively (``c_0`` is simpler).

When the leading coefficient cancels, the series precision is increased and the expansion is
repeated.

## Rebuilding the answer

A rational answer is returned as an `Int` or `Rational`, and an infinite one as `±Inf`.
Anything else is converted back from the canonical form by calling `build(op, args...)` for
each compound node, and `lift` for each number. By default `build` calls `op(args...)`,
except for `Expr` input, where it constructs an unevaluated call (see [`Expr` answers](@ref)),
and for term types such as SymbolicUtils, where a call on numbers only is built with
TermInterface's `maketerm` so that it stays exact.

## Limitations

* Only the functions listed in [Supported functions](@ref) are understood.
* The limit point is real, and so are all values; complex numbers are rejected.
* The sign of a constant is decided numerically (in `BigFloat`), and a constant that is zero
  to that precision is taken to be zero. Sines and cosines of rational multiples of ``\pi``
  with denominators 1, 2, 3, 4 and 6 are evaluated exactly.
* A free parameter is taken to be nonzero, of unknown sign. When the algorithm needs the sign
  of a constant that contains one, a [`GruntzError`](@ref) is thrown, unless the sign follows
  from those given with the experimental `signs` keyword (see
  [Parameters and their signs](@ref)). Where only the size of a limit matters, as when
  deciding that ``x^a`` and ``x`` are comparable, the sign is not needed.
* Comparable terms whose exponents have an irrational ratio, such as ``3^x`` and ``5^x``, are
  handled with irrational powers of ``\omega``; such powers are ordered by the sign of their
  difference.
