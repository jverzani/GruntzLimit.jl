# The limit problems, as quoted expressions, so each worker builds them with its
# own variables. Each entry is
#   (f, x0, dir, answer, source)
# `f` is in the variable `x`, with parameters `a` and `b`; `π` and `ℯ` are bound
# to each term type's exact constants. `x0` is `Inf`, `-Inf` or an expression;
# `dir` is `:+`, `:-` or `:both` (ignored at ±Inf). `answer` is a Julia expression
# for the limit, evaluated with the parameter values of core.jl (a, b > 0).
[
    # D. Gruntz, "On Computing Limits in a Symbolic Manipulation System", §8
    (:(exp(x)*(exp(1/x - exp(-x)) - exp(1/x))), Inf, :both, -1, "Gruntz 8.1"),
    (:(exp(x)*(exp(1/x + exp(-x) + exp(-x^2)) - exp(1/x - exp(-exp(x))))), Inf, :both, 1, "Gruntz 8.2"),
    (:(exp(exp(x - exp(-x))/(1 - 1/x)) - exp(exp(x))), Inf, :both, Inf, "Gruntz 8.3"),
    (:(exp(exp(exp(x)/(1 - 1/x))) - exp(exp(exp(x)/(1 - 1/x - log(x)^(-log(x)))))), Inf, :both, -Inf, "Gruntz 8.4"),
    (:(exp(exp(exp(x + exp(-x)))) / exp(exp(exp(x)))), Inf, :both, Inf, "Gruntz 8.5"),
    (:(exp(exp(exp(x))) / exp(exp(exp(x - exp(-exp(x)))))), Inf, :both, Inf, "Gruntz 8.6"),
    (:(exp(exp(exp(x))) / exp(exp(exp(x - exp(-exp(exp(x))))))), Inf, :both, 1, "Gruntz 8.7"),
    (:(exp(exp(x)) / exp(exp(x - exp(-exp(exp(x)))))), Inf, :both, 1, "Gruntz 8.8"),
    (:(log(x)^2 * exp(sqrt(log(x))*log(log(x))^2*exp(sqrt(log(log(x)))*log(log(log(x)))^3)) / sqrt(x)), Inf, :both, 0, "Gruntz 8.9"),
    (:((x*log(x)*log(x*exp(x) - x^2)^2) / log(log(x^2 + 2*exp(exp(3*x^3*log(x)))))), Inf, :both, 1//3, "Gruntz 8.10"),
    (:((exp(x*exp(-x)/(exp(-x) + exp(-2*x^2/(x + 1)))) - exp(x))/x), Inf, :both, :(-exp(2)), "Gruntz 8.11"),
    (:((3^x + 5^x)^(1/x)), Inf, :both, 5, "Gruntz 8.12"),
    (:(x/log(x^log(x^(log(2)/log(x))))), Inf, :both, Inf, "Gruntz 8.13"),
    (:(exp(exp(2*log(x^5 + x)*log(log(x)))) / exp(exp(10*log(x)*log(log(x))))), Inf, :both, Inf, "Gruntz 8.14"),
    (:(exp(exp(5//2*x^(-5//7) + 21//8*x^(6//11) + 2*x^(-8) + 54//17*x^(49//45)))^8 / log(log(-log(4//3*x^(-5//14))))^(7//6)), Inf, :both, Inf, "Gruntz 8.15"),
    (:((exp(4*x*exp(-x)/(1/exp(x) + 1/exp(2*x^2/(x + 1)))) - exp(x)) / exp(x)^4), Inf, :both, 1, "Gruntz 8.16"),
    (:(exp(x*exp(-x)/(exp(-x) + exp(-2*x^2/(x + 1))))/exp(x)), Inf, :both, 1, "Gruntz 8.17"),
    (:((exp(exp(-x/(1 + exp(-x))))*exp(-x/(1 + exp(-x/(1 + exp(-x)))))*exp(exp(-x + exp(-x/(1 + exp(-x))))))/exp(-x/(1 + exp(-x)))^2 - exp(x) + x), Inf, :both, 2, "Gruntz 8.18"),
    (:(log(x)*(log(log(x) + log(log(x))) - log(log(x)))/log(log(x) + log(log(log(x))))), Inf, :both, 1, "Gruntz 8.19"),
    (:(exp(log(log(x + exp(log(x)*log(log(x))))) / log(log(log(exp(x) + x + log(x)))))), Inf, :both, :(exp(1)), "Gruntz 8.20"),
    (:(exp(x)*(sin(1/x + exp(-x)) - sin(1/x + exp(-x^2)))), Inf, :both, 1, "Gruntz 8.21"),
    (:(exp(exp(x))*(exp(sin(1/x + exp(-exp(x)))) - exp(sin(1/x)))), Inf, :both, 1, "Gruntz 8.22"),
    (:(log(log(x*exp(x*exp(x)) + 1)) - exp(exp(log(log(x)) + 1/x))), Inf, :both, 0, "SymbolicLimits README"),

    # at infinity
    (:((1 + 1/x)^(x^2)/exp(x)), Inf, :both, :(exp(-1/2)), "rate of (1 + 1/x)^x"),
    (:(x*((1 + 1/x)^x - ℯ)), Inf, :both, :(-exp(1)/2), "rate of (1 + 1/x)^x"),
    (:((log(x + 1)/log(x))^(x*log(x))), Inf, :both, :(exp(1)), "1^∞ form"),
    (:(x - x^2*log(1 + 1/x)), Inf, :both, 1//2, "∞ − ∞"),
    (:(x^2*(exp(1/x) - exp(1/(x + 1)))), Inf, :both, 1, "cancellation"),
    (:(log(x)^log(x) / x^log(log(x))), Inf, :both, 1, "identically 1"),
    (:(sqrt(x + sqrt(x + sqrt(x))) - sqrt(x)), Inf, :both, 1//2, "nested radicals"),
    (:((x^(1/x) - 1)*x/log(x)), Inf, :both, 1, "x^(1/x)"),
    (:(log(1 + exp(x))/x), Inf, :both, 1, "log-exp"),
    (:(x^sin(1/x)), Inf, :both, 1, "∞⁰ form"),
    (:(x^2*(x*sin(1/x) - 1)), Inf, :both, -1//6, "series at ∞"),
    (:(x + sqrt(x^2 + x)), -Inf, :both, -1//2, "∞ − ∞ at −∞"),

    # at infinity, with parameters
    (:((1 + a/x)^(b*x)), Inf, :both, :(exp(a*b)), "parameters"),
    (:(x*(a^(1/x) - 1)), Inf, :both, :(log(a)), "parameters (a > 0)"),
    (:(x^a/exp(x)), Inf, :both, 0, "parameters"),
    (:(x*(log(x + a) - log(x))), Inf, :both, :a, "parameters"),
    (:(((x + a)/(x + b))^x), Inf, :both, :(exp(a - b)), "parameters"),
    (:(sqrt(x^2 + a*x + b) - x), Inf, :both, :(a/2), "parameters"),

    # at finite points
    (:((sin(tan(x)) - tan(sin(x)))/x^7), 0, :both, -1//30, "sin∘tan − tan∘sin"),
    (:((tan(tan(x)) - sin(sin(x)))/(tan(x) - sin(x))), 0, :both, 2, "Arnold"),
    (:((tan(x) - sin(x))/x^3), 0, :both, 1//2, "series"),
    (:((2*sin(x) - sin(2*x))/(x - sin(x))), 0, :both, 6, "series"),
    (:(1/x - 1/(exp(x) - 1)), 0, :both, 1//2, "∞ − ∞"),
    (:(cos(x)^(1/x^2)), 0, :both, :(exp(-1/2)), "1^∞ form"),
    (:((exp(sin(x)) - exp(x))/(sin(x) - x)), 0, :both, 1, "series"),
    (:((asin(x) - atan(x))/x^3), 0, :both, 1//2, "inverse trigonometric"),
    (:(exp(-1/x^2)/x^100), 0, :both, 0, "essential singularity"),
    (:(x^(x^x)), 0, :+, 0, "0^0 form, one-sided"),
    (:((x^x - 1)/(x*log(x))), 0, :+, 1, "one-sided"),
    (:(x*exp(1/x)), 0, :-, 0, "one-sided"),
    (:(1/log(x) - 1/(x - 1)), 1, :both, 1//2, "∞ − ∞"),
    (:(x^(1/(1 - x))), 1, :both, :(exp(-1)), "1^∞ form"),
    (:(tan(x)^tan(2*x)), :(π/4), :both, :(exp(-1)), "limit point π/4"),
    (:((π/2 - x)*tan(x)), :(π/2), :both, 1, "limit point π/2"),

    # at finite points, with parameters
    (:((a^x - b^x)/x), 0, :both, :(log(a) - log(b)), "parameters (a, b > 0)"),
    (:(sin(a*x)/sin(b*x)), 0, :both, :(a/b), "parameters"),
    (:((1 - cos(a*x))/x^2), 0, :both, :(a^2/2), "parameters"),
    (:((1 + a*x)^(1/x)), 0, :both, :(exp(a)), "parameters"),
    (:(log(cos(a*x))/log(cos(b*x))), 0, :both, :(a^2/b^2), "parameters"),
    (:((x^a - 1)/(x - 1)), 1, :both, :a, "parameters"),
    (:((exp(x) - exp(a))/(x - a)), :a, :both, :(exp(a)), "limit point a"),
    (:((sin(x) - sin(a))/(x - a)), :a, :both, :(cos(a)), "limit point a"),
    (:((x^x - a^a)/(x - a)), :a, :both, :(a^a*(log(a) + 1)), "limit point a (a > 0)"),
]
