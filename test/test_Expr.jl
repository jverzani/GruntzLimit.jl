# Julia `Expr` input: the variable (and any parameter) is a `Symbol`. Rational
# and infinite limits come back as numbers; others as unevaluated `Expr`s.

# evaluate a returned expression, binding the parameters `a` and `b`
ev(r; a = 2.0, b = 3.0) = eval(:(let a = $a, b = $b; $r end))

@testset "Expr" begin
    @testset "limits at Inf" begin
        @test gruntz_limit(:(x), :x) == Inf
        @test gruntz_limit(:(1/x), :x) == 0
        @test gruntz_limit(:(inv(x)), :x) == 0
        @test gruntz_limit(:(x^2 * exp(-x)), :x) == 0
        @test gruntz_limit(:(log(x)/x), :x) == 0
        @test gruntz_limit(:((x^2 + 1) / (2x^2 - 3)), :x) == 1//2
        @test gruntz_limit(:(sqrt(x^2 + x) - x), :x) == 1//2
        @test gruntz_limit(:(cbrt(x^3 + x^2) - x), :x) == 1//3
        @test gruntz_limit(:(exp(x + exp(-x)) - exp(x)), :x) == 1
        @test gruntz_limit(:(exp(x) / x^100), :x) == Inf
        @test gruntz_limit(:(-exp(x)), :x) == -Inf
        @test gruntz_limit(:(x * sin(1/x)), :x) == 1
        @test gruntz_limit(:(log(x + 1) - log(x)), :x, Inf) == 0
        @test gruntz_limit(:(x^x / exp(x)), :x) == Inf
        @test gruntz_limit(:(x^(1/x)), :x) == 1
        @test gruntz_limit(:(x - x), :x) == 0
        @test gruntz_limit(:(2.5x / x), :x) == 5//2
        @test gruntz_limit(:(x^2), :x, -Inf) == Inf
    end

    @testset "finite points and one-sided limits" begin
        @test gruntz_limit(:(sin(x)/x), :x, 0) == 1
        @test gruntz_limit(:((exp(x) - 1)/x), :x, 0) == 1
        @test gruntz_limit(:(1/x), :x, 0; dir = :+) == Inf
        @test gruntz_limit(:(1/x), :x, 0; dir = :-) == -Inf
        @test gruntz_limit(:(exp(1/x)), :x, 0; dir = :+) == Inf
        @test gruntz_limit(:(exp(1/x)), :x, 0; dir = :-) == 0
        @test gruntz_limit(:(x * log(x)), :x, 0) == 0
        @test gruntz_limit(:(x^x), :x, 0) == 1
        @test gruntz_limit(:(x + 1/x), :x, 3) == 10//3
        @test gruntz_limit(:((cos(sin(x)) - cos(x))/x^4), :x, 0) == 1//6
        @test gruntz_limit(:(1/x^2 - 1/sin(x)^2), :x, 0) == -1//3
    end

    @testset "hyperbolic and other functions" begin
        @test gruntz_limit(:(tan(x)/x), :x, 0) == 1
        @test gruntz_limit(:(sinh(x)/x), :x, 0) == 1
        @test gruntz_limit(:(tanh(x)), :x) == 1
        @test gruntz_limit(:(cosh(x)/exp(x)), :x) == 1//2
        r = gruntz_limit(:(log(2, x)/log(x)), :x)
        @test r isa Expr && ev(r) ≈ 1/log(2)
    end

    @testset "reciprocal and inverse trigonometric/hyperbolic functions" begin
        @test gruntz_limit(:(x * cot(x)), :x, 0) == 1
        @test gruntz_limit(:(sec(x)), :x, 0) == 1
        @test gruntz_limit(:(x * csc(x)), :x, 0) == 1
        @test gruntz_limit(:(cot(x) - 1/x), :x, 0) == 0
        @test gruntz_limit(:(coth(x)), :x) == 1
        @test gruntz_limit(:(x * coth(x)), :x, 0) == 1
        @test gruntz_limit(:(exp(x) * sech(x)), :x) == 2
        @test gruntz_limit(:(asin(x)/x), :x, 0) == 1
        @test gruntz_limit(:(asin(1/x) * x), :x) == 1
        @test gruntz_limit(:(asin(sin(x))/x), :x, 0) == 1
        @test gruntz_limit(:(acos(x)), :x, 1; dir = :-) == 0
        @test gruntz_limit(:(acos(x)), :x, -1; dir = :+) === π
        @test gruntz_limit(:(asec(x)), :x, 1; dir = :+) == 0
        @test gruntz_limit(:(acot(x)), :x) == 0
        @test gruntz_limit(:(acot(x)), :x, 0; dir = :+) == :($(1//2) * $π)
        @test gruntz_limit(:(asinh(x)/x), :x, 0) == 1
        @test gruntz_limit(:(sinh(asinh(x))/x), :x) == 1
        @test gruntz_limit(:(acosh(x) - log(x)), :x) == :(log(2))

        # constant answers are correct, though written in terms of atan, log, sqrt
        for (f, x0, val) in [(:(asin(x)), 1//2, π/6), (:(acos(x)), 1//2, π/3),
                             (:(acsc(x)), 2, π/6), (:(tanh(atanh(x))), 1//2, 1/2)]
            @test ev(gruntz_limit(f, :x, x0)) ≈ val
        end

        # complex-valued near the limit point
        @test_throws GruntzError gruntz_limit(:(asin(x)), :x, 1; dir = :+)
        @test_throws GruntzError gruntz_limit(:(acosh(x)), :x, 0)
    end

    @testset "exact Expr results" begin
        @test gruntz_limit(:((1 + 1/x)^x), :x) == :(exp(1))
        @test gruntz_limit(:(atan(x)), :x) == :($(1//2) * $π)
        @test gruntz_limit(:(atan(x)), :x, -Inf) == :($(-1//2) * $π)
        @test gruntz_limit(:(atan(1/x)), :x, 0; dir = :-) == :($(-1//2) * $π)
        @test gruntz_limit(:(sqrt(x)), :x, 2) == :(sqrt(2))

        for (f, x0, kw, val) in [
                (:(atan(exp(x))), Inf, (;), π/2),
                (:(atan(x^2 - x)), Inf, (;), π/2),
                (:(atan(1/x)), 0, (dir = :+,), π/2),
                (:((sin(x)/x)^(1/x^2)), 0, (;), exp(-1/6)),
                (:(sqrt(1 - cos(2x))/x), 0, (dir = :+,), sqrt(2)),
                (:(sqrt(1 - cos(2x))/x), 0, (dir = :-,), -sqrt(2)),
            ]
            r = gruntz_limit(f, :x, x0; kw...)
            @test r isa Expr
            @test ev(r) ≈ val
        end
        @test eval(gruntz_limit(:(atan(x)), :x)) ≈ π/2
    end

    @testset "arctangent" begin
        @test gruntz_limit(:(atan(x)/x), :x) == 0
        @test gruntz_limit(:(x * atan(1/x)), :x) == 1
        @test gruntz_limit(:(x^2 * (atan(x + 1) - atan(x))), :x) == 1
        @test gruntz_limit(:(atan(x)/x), :x, 0) == 1
        @test gruntz_limit(:((atan(x) - x)/x^3), :x, 0) == -1//3
    end

    @testset "absolute value" begin
        @test gruntz_limit(:(x/abs(x)), :x, 0; dir = :+) == 1
        @test gruntz_limit(:(x/abs(x)), :x, 0; dir = :-) == -1
        @test_throws GruntzError gruntz_limit(:(x/abs(x)), :x, 0; dir = :both)
        @test gruntz_limit(:(abs(x)), :x, 0) == 0
        @test gruntz_limit(:(abs(x)), :x, -Inf) == Inf
        @test gruntz_limit(:(abs(x)/x), :x, -Inf) == -1
        @test gruntz_limit(:(abs(x - 1)/(x - 1)), :x, 1; dir = :-) == -1
        @test gruntz_limit(:(abs(sin(x))/x), :x, 0; dir = :+) == 1
        @test gruntz_limit(:(abs(x^2 - 4)/(x - 2)), :x, 2; dir = :+) == 4
        @test gruntz_limit(:(abs(x^2 - 4)/(x - 2)), :x, 2; dir = :-) == -4
    end

    @testset "parameters" begin
        @test gruntz_limit(:((1 + a/x)^x), :x) == :(exp(a))
        @test gruntz_limit(:(sqrt(x^2 + a*x) - x), :x) == :($(1//2) * a)
        @test gruntz_limit(:(sin(a*x)/x), :x, 0) == :a
        @test gruntz_limit(:((x^x - x^a)/(a^x - a^a)), :x, :a) == 1

        # parameter or expression as the limit point
        r = gruntz_limit(:(x^2 + a*x), :x, :a)
        @test r isa Expr && ev(r; a = 3) ≈ 18
        r = gruntz_limit(:(exp(x)/x), :x, :b)
        @test r isa Expr && ev(r; b = 3) ≈ exp(3)/3
        r = gruntz_limit(:(x^2), :x, :(a + 1))
        @test r isa Expr && ev(r; a = 3) ≈ 16
    end

    @testset "signs of parameters (experimental)" begin
        @test gruntz_limit(:(x^a * exp(-b*x)), :x; signs = Dict(:a => 1, :b => 1)) == 0
        @test gruntz_limit(:(exp(a*b*x)), :x; signs = Dict(:a => 1, :b => -1)) == 0
        @test gruntz_limit(:(x^a), :x, 0; signs = [:a => 1]) == 0
        @test_throws GruntzError gruntz_limit(:(x^a), :x, 0)
    end

    @testset "constants pi, π and ℯ" begin
        # bare symbols are constants, not free parameters, so their sign is known
        @test gruntz_limit(:(exp(pi*x)), :x) == Inf
        @test gruntz_limit(:(exp(-π*x)), :x) == 0
        @test gruntz_limit(:(x^ℯ / exp(x)), :x) == 0
        @test gruntz_limit(:(log(ℯ*x) - log(x)), :x) == 1
        @test gruntz_limit(:(atan(x) - pi/2), :x) == 0
        @test gruntz_limit(:(x * (atan(x) - pi/2)), :x) == -1
        @test gruntz_limit(:(x/(x - pi)), :x, :pi) == Inf
        @test gruntz_limit(:(pi*x/x), :x, 0) === π
        @test gruntz_limit(:(sin(π*x)/x), :x, 0) === π
        @test gruntz_limit(:((1 + ℯ/x)^x), :x) == :(exp(exp(1)))
    end

    @testset "trigonometric functions at multiples of π" begin
        @test gruntz_limit(:(tan(x)^tan(2x)), :x, :(π/4); dir = :both) == :(exp(1) ^ -1)
        @test ev(gruntz_limit(:(sin(x - π/4)/(cos(x) - sin(x))), :x, :(π/4); dir = :both)) ≈ -1/sqrt(2)
        @test gruntz_limit(:(cos(π/3) + x), :x, 0) == 1//2
    end

    @testset "irrational ratio of exponents" begin
        @test ev(gruntz_limit(:((2^x - 1)/(3^x - 1)), :x, 0; dir = :both)) ≈ log(2)/log(3)
        @test gruntz_limit(:((2^(1/x) + 3^(1/x))^x), :x, 0) == 3
    end

    @testset "rational literals" begin
        @test gruntz_limit(:(x^(5//7)/x), :x) == 0
        @test gruntz_limit(:(sin(x)/x + 1//3), :x, 0) == 4//3
        @test gruntz_limit(:(exp(exp(5//2*x^(-5//7) + 21//8*x^(6//11) + 2*x^(-8) + 54//17*x^(49//45)))^8 /
                             log(log(-log(4//3*x^(-5//14))))^(7//6)), :x) == Inf
    end

    @testset "custom build" begin
        # calling the operations instead evaluates constant answers
        callop = (op, args...) -> op(args...)
        @test gruntz_limit(:((1 + 1/x)^x), :x; build = callop) ≈ exp(1)
        @test gruntz_limit(:(atan(x)), :x; build = callop) ≈ π/2
    end

    @testset "errors" begin
        @test_throws GruntzError gruntz_limit(:(sin(x)), :x)
        @test_throws GruntzError gruntz_limit(:(sin(1/x)), :x, 0)
        @test_throws GruntzError gruntz_limit(:(gamma(x)), :x)
        @test_throws GruntzError gruntz_limit(:(log(x)), :x, -1)
        @test_throws GruntzError gruntz_limit(:(sqrt(-1 - x^2)), :x)
        @test_throws GruntzError gruntz_limit(:(1/x), :x, 0; dir = :sideways)
    end
end
