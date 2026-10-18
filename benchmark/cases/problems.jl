# Limits whose value depends on the parameters a and b, as quoted expressions.
# Each entry is
#   (f, x0, dir, cases, source)
# with `f` in the variable `x`, `x0` `Inf`, `-Inf` or an expression, `dir` `:+`,
# `:-` or `:both` (ignored at ±Inf), and `cases` a vector of
#   (condition, sample, answer)
# `condition` is an expression in a and b; `sample` a NamedTuple of parameter values
# satisfying it, used by check_problems.jl to confirm the answer numerically;
# `answer` a number, ±Inf, an expression in the parameters, or
#   :nolimit     the limit does not exist (oscillation, or one-sided limits differ)
#   :undefined   f is not defined near x0 (e.g. a^x for a < 0)
# The conditions of a problem cover every real value of the parameters, so a
# method that splits into cases can be checked for completeness, not only for
# each answer. Where a parameter's domain is restricted (a > 0 for a^x), the
# rest is listed as :undefined.
[
    # a power of x: the sign of the exponent decides
    (:(x^a), Inf, :both,
     [(:(a < 0), (a = -1.5,), 0), (:(a == 0), (a = 0,), 1), (:(a > 0), (a = 1.5,), Inf)],
     "x^a, the basic case"),
    (:(x^(a - 2)), Inf, :both,
     [(:(a < 2), (a = 1.5,), 0), (:(a == 2), (a = 2,), 1), (:(a > 2), (a = 2.5,), Inf)],
     "sign of a - 2, not of a"),
    (:(x^a), 0, :+,
     [(:(a < 0), (a = -1.5,), Inf), (:(a == 0), (a = 0,), 1), (:(a > 0), (a = 1.5,), 0)],
     "x^a at 0⁺"),
    (:(x^a*log(x)), 0, :+,
     [(:(a <= 0), (a = -0.5,), -Inf), (:(a > 0), (a = 0.5,), 0)],
     "a = 0 joins a < 0"),
    (:(log(x)/x^a), Inf, :both,
     [(:(a <= 0), (a = -0.5,), Inf), (:(a > 0), (a = 0.5,), 0)],
     "log against a power"),
    (:(x^a - x^b), Inf, :both,
     [(:(a < b && b > 0), (a = 1, b = 2), -Inf), (:(a > b && a > 0), (a = 2, b = 1), Inf),
      (:(a == b), (a = 1.5, b = 1.5), 0),
      (:(a < b && b == 0), (a = -1, b = 0), -1), (:(a > b && a == 0), (a = 0, b = -1), 1),
      (:(a < b && b < 0), (a = -2, b = -1), 0), (:(a > b && a < 0), (a = -1, b = -2), 0)],
     "two exponents compared, and with 0"),
    (:(x^a/(1 + x^b)), Inf, :both,
     [(:(b > 0 && a < b), (a = 1, b = 2), 0), (:(b > 0 && a == b), (a = 2, b = 2), 1), (:(b > 0 && a > b), (a = 3, b = 2), Inf),
      (:(b == 0 && a < 0), (a = -1, b = 0), 0), (:(b == 0 && a == 0), (a = 0, b = 0), 1//2), (:(b == 0 && a > 0), (a = 1, b = 0), Inf),
      (:(b < 0 && a < 0), (a = -1, b = -1), 0), (:(b < 0 && a == 0), (a = 0, b = -1), 1), (:(b < 0 && a > 0), (a = 1, b = -1), Inf)],
     "nested cases: b, then a against max(b, 0)"),

    # exponentials and bases
    (:(exp(a*x)), Inf, :both,
     [(:(a < 0), (a = -1.5,), 0), (:(a == 0), (a = 0,), 1), (:(a > 0), (a = 1.5,), Inf)],
     "exp(a x)"),
    (:(x^a/exp(b*x)), Inf, :both,
     [(:(b > 0), (a = 3, b = 0.5), 0), (:(b < 0), (a = -3, b = -0.5), Inf),
      (:(b == 0 && a < 0), (a = -1, b = 0), 0), (:(b == 0 && a == 0), (a = 0, b = 0), 1), (:(b == 0 && a > 0), (a = 1, b = 0), Inf)],
     "b decides unless b = 0, then a"),
    (:(a^x), Inf, :both,
     [(:(a <= 0), (a = -2,), :undefined), (:(0 < a < 1), (a = 0.5,), 0), (:(a == 1), (a = 1,), 1), (:(a > 1), (a = 2,), Inf)],
     "the sign of log(a)"),
    (:((a^x + b^x)^(1/x)), Inf, :both,
     [(:(a <= 0 || b <= 0), (a = -1, b = 2), :undefined), (:(0 < a < b), (a = 2, b = 3), :b), (:(0 < b <= a), (a = 3, b = 2), :a)],
     "max(a, b), generalising Gruntz 8.12"),
    (:((x^a + 1)^(1/log(x))), Inf, :both,
     [(:(a <= 0), (a = -1,), 1), (:(a > 0), (a = 1.5,), :(exp(a)))],
     "exp(max(a, 0))"),

    # leading coefficients that may vanish
    (:(sqrt(x^2 + a*x) - b*x), Inf, :both,
     [(:(b < 1), (a = 2, b = 0.5), Inf), (:(b == 1), (a = 2, b = 1), :(a/2)), (:(b > 1), (a = 2, b = 1.5), -Inf)],
     "cancellation only for b = 1"),
    (:((a*x^2 + x)/(b*x^2 + 1)), Inf, :both,
     [(:(b != 0), (a = 2, b = 3), :(a/b)),
      (:(b == 0 && a > 0), (a = 2, b = 0), Inf), (:(b == 0 && a < 0), (a = -2, b = 0), -Inf), (:(b == 0 && a == 0), (a = 0, b = 0), Inf)],
     "rational function, leading coefficients a and b"),
    (:(sin(a*x)/sin(b*x)), 0, :both,
     [(:(b != 0), (a = 2, b = 3), :(a/b)), (:(b == 0), (a = 2, b = 0), :undefined)],
     "a/b needs b ≠ 0"),
    (:(atan(a*x)), Inf, :both,
     [(:(a < 0), (a = -1.5,), :(-π/2)), (:(a == 0), (a = 0,), 0), (:(a > 0), (a = 1.5,), :(π/2))],
     "atan(a x)"),

    # existence depends on the parameter
    (:(x^a*sin(1/x)), 0, :+,
     [(:(a <= 0), (a = -0.5,), :nolimit), (:(a > 0), (a = 0.5,), 0)],
     "oscillation damped only for a > 0"),
    (:(abs(x)/x), :a, :both,
     [(:(a < 0), (a = -1,), -1), (:(a == 0), (a = 0,), :nolimit), (:(a > 0), (a = 1,), 1)],
     "the limit point is the parameter"),
    (:(1/(x - a)), 0, :both,
     [(:(a != 0), (a = 2,), :(-1/a)), (:(a == 0), (a = 0,), :nolimit)],
     "a pole at the limit point when a = 0"),
]
