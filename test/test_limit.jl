# Shared by the SymEngine, SymbolicUtils and SimpleExpressions tests. The including file defines the
# variables `x`, `a` and the exact constants `ONE` (one) and `PI` (π) of the package.
# Symbolic answers are compared with `isequal`, as `==` builds an equation for
# some packages (SymbolicUtils).
@testset "limits via Gruntz's algorithm" begin
    @test gruntz_limit(x, x) == Inf
    @test gruntz_limit(1/x, x) == 0
    @test gruntz_limit(x^2 * exp(-x), x) == 0
    @test gruntz_limit(log(x)/x, x) == 0
    @test gruntz_limit((x^2 + 1) / (2x^2 - 3), x) == 1//2
    @test gruntz_limit(sqrt(x^2 + x) - x, x) == 1//2
    @test gruntz_limit(exp(x + exp(-x)) - exp(x), x) == 1
    @test gruntz_limit(exp(x) / x^100, x) == Inf
    @test gruntz_limit(-exp(x), x) == -Inf
    @test gruntz_limit(x * sin(1/x), x) == 1
    @test gruntz_limit(log(x + 1) - log(x), x) == 0
    @test gruntz_limit(x^x / exp(x), x) == Inf
    @test gruntz_limit(x - x, x) == 0
    @test isequal(gruntz_limit((1 + 1/x)^x, x), exp(ONE))
    @test isequal(gruntz_limit((1 + a/x)^x, x), exp(a))

    # finite points, one-sided limits, -Inf
    @test gruntz_limit(sin(x)/x, x, 0) == 1
    @test gruntz_limit((exp(x) - 1)/x, x, 0) == 1
    @test gruntz_limit(1/x, x, 0; dir = :+) == Inf
    @test gruntz_limit(1/x, x, 0; dir = :-) == -Inf
    @test gruntz_limit(x^2, x, -Inf) == Inf

    @test gruntz_limit(x + 1/x, x, 3) == 10//3
    @test gruntz_limit(x * log(x), x, 0) == 0
    @test gruntz_limit(x^x, x, 0) == 1
    @test gruntz_limit(cbrt(x^3 + x^2) - x, x) == 1//3
    @test gruntz_limit(x^(1/x), x) == 1
    @test gruntz_limit(2.5x / x, x) == 5//2

    # tangent and hyperbolic functions
    @test gruntz_limit(tan(x)/x, x, 0) == 1
    @test gruntz_limit(sinh(x)/x, x, 0) == 1
    @test gruntz_limit(tanh(x), x) == 1
    @test gruntz_limit(cosh(x)/exp(x), x) == 1//2

    # arctangent
    @test isequal(gruntz_limit(atan(x), x), (1//2) * PI)
    @test isequal(gruntz_limit(atan(x), x, -Inf), (-1//2) * PI)
    @test isequal(gruntz_limit(atan(exp(x)), x), (1//2) * PI)
    @test gruntz_limit(atan(x)/x, x) == 0
    @test gruntz_limit(x * atan(1/x), x) == 1
    @test gruntz_limit(x^2 * (atan(x + 1) - atan(x)), x) == 1
    @test isequal(gruntz_limit(atan(1/x), x, 0; dir = :+), (1//2) * PI)
    @test isequal(gruntz_limit(atan(1/x), x, 0; dir = :-), (-1//2) * PI)
    @test gruntz_limit(atan(x)/x, x, 0) == 1
    @test gruntz_limit((atan(x) - x)/x^3, x, 0) == -1//3
    @test isequal(gruntz_limit(atan(x^2 - x), x), (1//2) * PI)

    # absolute value (resolved from the sign near the limit point)
    @test gruntz_limit(x/abs(x), x, 0; dir = :+) == 1
    @test gruntz_limit(x/abs(x), x, 0; dir = :-) == -1
    @test_throws GruntzError gruntz_limit(x/abs(x), x, 0; dir = :both)
    @test gruntz_limit(abs(x), x, 0) == 0
    @test gruntz_limit(abs(x), x, -Inf) == Inf
    @test gruntz_limit(abs(x)/x, x, -Inf) == -1
    @test gruntz_limit(abs(x - 1)/(x - 1), x, 1; dir = :-) == -1
    @test gruntz_limit(abs(sin(x))/x, x, 0; dir = :+) == 1
    @test gruntz_limit(abs(x^2 - 4)/(x - 2), x, 2; dir = :+) == 4
    @test gruntz_limit(abs(x^2 - 4)/(x - 2), x, 2; dir = :-) == -4

    # harder ones?
    @test gruntz_limit((cos(sin(x))-cos(x))/x^4, x, 0) == 1//6
    @test gruntz_limit((x^x - x^a)/(a^x - a^a), x, a) == 1
    @test isequal(gruntz_limit((sin(x)/x)^(1/x^2), x, 0), 1/exp(ONE)^(1//6))
    @test gruntz_limit(1/x^2 - 1/sin(x)^2, x, 0) == - 1//3
    @test isequal(gruntz_limit(sqrt(1 - cos(2x))/x, x, 0; dir = :+), sqrt(2ONE))
    @test isequal(gruntz_limit(sqrt(1 - cos(2x))/x, x, 0; dir = :-), -sqrt(2ONE))

    # reciprocal trigonometric and hyperbolic functions
    @test gruntz_limit(x * cot(x), x, 0) == 1
    @test gruntz_limit((sec(x) - 1)/x^2, x, 0) == 1//2
    @test gruntz_limit(csc(x) - cot(x), x, 0) == 0
    @test gruntz_limit(csc(x), x, 0; dir = :-) == -Inf
    @test gruntz_limit(sech(x), x) == 0
    @test gruntz_limit(x * csch(x), x, 0) == 1
    @test gruntz_limit(coth(x), x, -Inf) == -1
    @test gruntz_limit(exp(x) * sech(x), x) == 2
    @test gruntz_limit(exp(x) / cosh(x), x) == 2

    # inverse trigonometric functions
    @test gruntz_limit((asin(x) - x)/x^3, x, 0) == 1//6
    @test isequal(gruntz_limit(asin(x), x, 1; dir = :-), (1//2) * PI)
    @test isequal(gruntz_limit(acos(x), x, -1; dir = :+), PI)
    @test isequal(gruntz_limit(acos(x)/sqrt(1 - x), x, 1; dir = :-), sqrt(2ONE))
    @test isequal(gruntz_limit(asec(x), x), (1//2) * PI)
    @test gruntz_limit(x * acsc(x), x) == 1
    @test gruntz_limit(x * acot(x), x) == 1
    @test isequal(gruntz_limit(acot(x), x, 0; dir = :-), (-1//2) * PI)

    # inverse hyperbolic functions
    @test isequal(gruntz_limit(asinh(x) - log(x), x), log(2ONE))
    @test isequal(gruntz_limit(acosh(x)/sqrt(x - 1), x, 1; dir = :+), sqrt(2ONE))
    @test gruntz_limit(atanh(x)/x, x, 0) == 1
    @test gruntz_limit(atanh(x), x, 1; dir = :-) == Inf
    @test gruntz_limit(asech(x), x, 0; dir = :+) == Inf
    @test gruntz_limit(x * acsch(x), x) == 1
    @test gruntz_limit(x * acoth(x), x) == 1

    # bounded oscillation has no limit
    @test_throws GruntzError gruntz_limit(sin(x), x)
end
