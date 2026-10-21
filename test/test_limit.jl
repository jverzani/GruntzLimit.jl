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

    # floor and ceil: constant near the limit point, with jumps at integers
    @test gruntz_limit(floor(x), x, 0; dir = :+) == 0
    @test gruntz_limit(floor(x), x, 0; dir = :-) == -1
    @test_throws GruntzError gruntz_limit(floor(x), x, 0; dir = :both)
    @test gruntz_limit(ceil(x), x, 0; dir = :+) == 1
    @test gruntz_limit(ceil(x), x, 0; dir = :-) == 0
    @test gruntz_limit(floor(x), x, 1//2) == 0
    @test gruntz_limit(floor(x^2), x, 0; dir = :-) == 0
    @test gruntz_limit(floor(sin(x)/x), x, 0) == 0
    @test gruntz_limit(ceil(cos(x)), x, 0) == 1
    @test gruntz_limit(floor(PI + 1/x), x) == 3
    @test gruntz_limit(floor(-1/x), x) == -1
    @test_throws GruntzError gruntz_limit(floor(x), x)

    # sign: the eventual sign of its argument
    @test gruntz_limit(sign(x), x, 0; dir = :+) == 1
    @test gruntz_limit(sign(x), x, 0; dir = :-) == -1
    @test_throws GruntzError gruntz_limit(sign(x), x, 0; dir = :both)
    @test gruntz_limit(sign(x - x^2), x) == -1
    @test gruntz_limit(sign(sin(x)), x, 0; dir = :-) == -1
    @test gruntz_limit(x * sign(x), x, 0; dir = :-) == 0

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

    # trigonometric functions at rational multiples of π (cos(π/2) is zero)
    @test gruntz_limit((PI/2 - x)*tan(x), x, PI/2; dir = :both) == 1
    @test gruntz_limit(cos(x)/(x - PI/2), x, PI/2; dir = :both) == -1
    @test gruntz_limit(sin(x)/(x - PI), x, PI; dir = :both) == -1
    @test gruntz_limit(sin(x)^2/(1 + cos(x)), x, PI; dir = :both) == 2

    # comparable exponentials with an irrational ratio of exponents
    @test gruntz_limit((2^x + 3^x)/3^x, x) == 1
    @test gruntz_limit(x^100 * 2^x/3^x, x) == 0
    @test gruntz_limit((3^x + 5^x)^(1/x), x) == 5
    @test gruntz_limit((2^x + 3^x)^(1/x), x, -Inf) == 2
    @test gruntz_limit(exp(exp(exp(x + exp(-x))))/exp(exp(exp(x))), x) == Inf

    # a parameter whose sign does not matter, and one whose sign does
    @test gruntz_limit(x^a/exp(x), x) == 0
    @test gruntz_limit(exp(x)/x^a, x) == Inf
    @test gruntz_limit(log(x)^a/x, x) == 0
    @test_throws GruntzError gruntz_limit(x^a/x^2, x)
    @test_throws GruntzError gruntz_limit(exp(a*x), x)

    # signs of parameters, given with `signs` (experimental)
    @test gruntz_limit(x^a, x; signs = Dict(a => :positive)) == Inf
    @test gruntz_limit(x^a, x; signs = Dict(a => :negative)) == 0
    @test gruntz_limit(x^a, x, 0; signs = Dict(a => :positive)) == 0
    @test gruntz_limit(exp(a*x), x; signs = [a => :negative]) == 0
    @test gruntz_limit(x^100 * exp(-a*x), x; signs = Dict(a => :positive)) == 0
    @test gruntz_limit((2a + 1)*x, x; signs = Dict(a => :positive)) == Inf
    @test gruntz_limit(x^(2 + a), x; signs = Dict(a => :positive)) == Inf
    @test_throws GruntzError gruntz_limit(x^(a - 2), x; signs = Dict(a => :positive))   # a > 0 is not enough
    @test gruntz_limit(x^(a - 2), x; signs = Dict(a - 2 => :positive)) == Inf       # a constant as key
    @test gruntz_limit(x^(a - 2), x; signs = Dict(a - 2 => :negative)) == 0
    @test gruntz_limit(a*x + 1, x; signs = Dict(a => :zero)) == 1                 # 0 substitutes
    @test_throws ArgumentError gruntz_limit(a*x, x; signs = Dict(a => 1))      # a Symbol is wanted
    @test_throws ArgumentError gruntz_limit(a*x, x; signs = Dict(a => :big))

    # a limit for each case of a parameter (experimental)
    cs = gruntz_cases(x^(a - 2), x)
    @test length(cs) == 3
    @test sort([v for (_, v) in cs]) == [0, 1, Inf]
    @test all(conds -> length(conds) == 1 && conds[1].rel in (:<, :(==), :>), first.(cs))
    @test cs(a => 3) == Inf && cs(a => 2) == 1 && cs(Dict(a => 1)) == 0
    @test cs[a => 3] === cs[end]

    # bounded oscillation has no limit
    @test_throws GruntzError gruntz_limit(sin(x), x)
end
