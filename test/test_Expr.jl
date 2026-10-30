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

    @testset "error function" begin
        @test gruntz_limit(:(erf(x)), :x) == 1
        @test gruntz_limit(:(erf(x)), :x, -Inf) == -1
        @test gruntz_limit(:(erfc(x)), :x) == 0
        @test gruntz_limit(:(erf(x)), :x, 1) == :(erf(1))
        @test ev(gruntz_limit(:(erf(x)/x), :x, 0)) ≈ 2/sqrt(π)
        @test ev(gruntz_limit(:((erf(x) - 2x/sqrt(pi))/x^3), :x, 0)) ≈ -2/(3sqrt(π))
        @test ev(gruntz_limit(:((erf(x + 1) - erf(1))/x), :x, 0)) ≈ 2/(sqrt(π)*ℯ)
        @test ev(gruntz_limit(:(erf(1/x)*x), :x)) ≈ 2/sqrt(π)
        # erf(u) = 1 - exp(-u^2) erfs(u) for u -> oo: the exponential is in the mrv set
        @test ev(gruntz_limit(:(x*exp(x^2)*erfc(x)), :x)) ≈ 1/sqrt(π)
        @test ev(gruntz_limit(:(x*exp(x^2)*(1 + erf(x))), :x, -Inf)) ≈ -1/sqrt(π)
        @test ev(gruntz_limit(:(x^2*exp(x^4)*(1 - erf(x^2))), :x)) ≈ 1/sqrt(π)
        @test ev(gruntz_limit(:(x^3*(exp(x^2)*erfc(x) - 1/(sqrt(pi)*x))), :x)) ≈ -1/(2sqrt(π))
        @test gruntz_limit(:(log(erfc(x))/x^2), :x) == -1
        @test gruntz_limit(:(erf(exp(x))^exp(x^2)), :x) == 1
        # erfs of an argument that is a constant for w but tends to infinity with x
        @test ev(gruntz_limit(:((erf(x - exp(-x)) - erf(x))*exp(x^2 + x)), :x)) ≈ -2/sqrt(π)
        @test gruntz_limit(:(erf(a*x)), :x; signs = Dict(:a => :negative)) == -1
        @test [join(string.(c.first), ", ") => c.second for c in gruntz_cases(:(erf(a*x)), :x)] ==
              ["a < 0" => -1, "a == 0" => 0, "a > 0" => 1]
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

    @testset "floor and ceil" begin
        @test gruntz_limit(:(floor(x)), :x, 0; dir = :+) == 0
        @test gruntz_limit(:(floor(x)), :x, 0; dir = :-) == -1
        @test_throws GruntzError gruntz_limit(:(floor(x)), :x, 0; dir = :both)
        @test gruntz_limit(:(ceil(x)), :x, 0; dir = :+) == 1
        @test gruntz_limit(:(ceil(x)), :x, 0; dir = :-) == 0
        @test gruntz_limit(:(floor(x)), :x, 2; dir = :-) == 1
        @test gruntz_limit(:(ceil(x)), :x, 2; dir = :+) == 3
        @test gruntz_limit(:(floor(x)), :x, 1//2) == 0
        @test gruntz_limit(:(floor(x)), :x, π) == 3
        @test gruntz_limit(:(floor(cos(x))), :x, 0) == 0
        @test gruntz_limit(:(floor(1 - exp(-x))), :x) == 0
        @test gruntz_limit(:(floor(exp(-x) + 1)), :x) == 1
        # an integer limit recognised numerically, approached from above
        @test gruntz_limit(:(floor(log(8)/log(2) + 1/x)), :x) == 3
        # nested, and inside abs
        @test gruntz_limit(:(floor(floor(x)/2 + x)), :x, 1; dir = :-) == 0
        @test gruntz_limit(:(abs(floor(x) - 1/2)), :x, 0; dir = :-) == 3//2
        @test gruntz_limit(:(floor(7//2) + floor(x)), :x, 0; dir = :+) == 3
        # a constant with a parameter stays; a limit point with one is an error
        @test gruntz_limit(:(floor(a) * x / x), :x) == :(floor(a))
        @test_throws GruntzError gruntz_limit(:(floor(a + 1/x)), :x)
        # the side of the jump depends on the sign of a parameter
        @test gruntz_limit(:(floor(1 + a/x)), :x; signs = Dict(:a => :negative)) == 0
        cs = gruntz_cases(:(floor(1 + a/x)), :x)
        @test [string(only(c.first)) => c.second for c in cs] == ["a < 0" => 0, "a >= 0" => 1]
        # a diverging argument (bounded oscillation of the fractional part)
        @test_throws GruntzError gruntz_limit(:(floor(x)), :x)
        @test_throws GruntzError gruntz_limit(:(x * floor(1/x)), :x, 0; dir = :+)
    end

    @testset "sign" begin
        @test gruntz_limit(:(sign(x)), :x, 0; dir = :+) == 1
        @test gruntz_limit(:(sign(x)), :x, 0; dir = :-) == -1
        @test_throws GruntzError gruntz_limit(:(sign(x)), :x, 0; dir = :both)
        # the argument may diverge; only its eventual sign matters
        @test gruntz_limit(:(sign(x^2 - x)), :x) == 1
        @test gruntz_limit(:(sign(exp(-x) - exp(-2x))), :x) == 1
        @test gruntz_limit(:(sign(x - 1) / sign(x - 2)), :x, 3//2) == -1
        @test_throws GruntzError gruntz_limit(:(sign(sin(x))), :x)      # no eventual sign
        # constants
        @test gruntz_limit(:(sign(pi - 3) * x / x), :x) == 1
        @test gruntz_limit(:(sign(-2) + sign(0)), :x) == -1
        # nested, with abs and floor
        @test gruntz_limit(:(abs(sign(x - 1))), :x, 1; dir = :-) == 1
        @test gruntz_limit(:(sign(floor(x) - 1/2)), :x, 1; dir = :-) == -1
        # parameters: a constant sign stays; otherwise cases on the sign of the parameter
        @test gruntz_limit(:(sign(a) * x / x), :x) == :(sign(a))
        @test gruntz_limit(:(sign(a*x)), :x; signs = Dict(:a => :negative)) == -1
        @test_throws GruntzError gruntz_limit(:(sign(a*x)), :x)
        shown(cs) = [join(string.(c.first), ", ") => c.second for c in cs]
        @test shown(gruntz_cases(:(sign(a*x)), :x)) == ["a < 0" => -1, "a == 0" => 0, "a > 0" => 1]
        @test shown(gruntz_cases(:(x^sign(a)), :x)) == ["a < 0" => 0, "a == 0" => 1, "a > 0" => Inf]
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

        # a = -(-a): powers of a and of -a are joined, so these zeros are recognised
        @test gruntz_limit(:(a/sqrt(-a) + sqrt(-a)), :x) == 0
        @test gruntz_limit(:((a/sqrt(-a) + sqrt(-a))*exp(x) + 1), :x) == 1
        @test gruntz_limit(:((a/sqrt(-2a) + sqrt(-2a)/2)*x), :x) == 0
        @test gruntz_limit(:((a*b/sqrt(-a*b) + sqrt(-a*b))*x), :x) == 0
        @test gruntz_limit(:((a/cbrt(-a) + cbrt(-a)^2)*x), :x) == 0
        @test gruntz_limit(:((1/sqrt(2) - sqrt(2)/2)*a*x), :x) == 0
        @test gruntz_limit(:((a/sqrt(-a))*x), :x) == -Inf
    end

    @testset "signs of parameters (experimental)" begin
        @test gruntz_limit(:(x^a * exp(-b*x)), :x; signs = Dict(:a => :positive, :b => :positive)) == 0
        @test gruntz_limit(:(exp(a*b*x)), :x; signs = Dict(:a => :positive, :b => :negative)) == 0
        @test gruntz_limit(:(x^a), :x, 0; signs = [:a => :positive]) == 0
        @test_throws GruntzError gruntz_limit(:(x^a), :x, 0)
        @test (try gruntz_limit(:(x^a), :x, 0) catch e; e.kind end) === :sign
        @test gruntz_limit(:(x^a - x^b), :x; signs = Dict(:(a - b) => :positive, :b => :positive)) == Inf
        # signs that rule out a log or a fractional power make the limit undefined;
        # without them, a parameter is generic
        neg = Dict(:a => :negative)
        @test_throws GruntzError gruntz_limit(:(log(a*x)/x), :x; signs = neg)
        @test_throws GruntzError gruntz_limit(:(log(-a*x)*x), :x, 0; dir = :-, signs = neg)
        @test gruntz_limit(:(log(-a*x)*x), :x, 0; dir = :-, signs = Dict(:a => :positive)) == 0
        @test_throws GruntzError gruntz_limit(:(sqrt(a)*x + x), :x; signs = neg)
        @test_throws GruntzError gruntz_limit(:(x/sqrt(a - 1)), :x; signs = Dict(:(a - 1) => :negative))
        @test gruntz_limit(:(sqrt(a)*x), :x; signs = Dict(:a => :nonnegative)) == Inf
        @test gruntz_limit(:(sqrt(a)*x + x), :x) == Inf
        @test (try gruntz_limit(:(log(a*x)/x), :x; signs = neg) catch e; e.kind end) === :undefined
        # a product of parameters is split into logs and powers of positive factors
        nn = Dict(:a => :negative, :b => :negative)
        @test gruntz_limit(:(log(a*b*x) - log(x)), :x; signs = nn) == :(log(-1a) + log(-1b))
        @test gruntz_limit(:(log(a*b*x) - log(x)), :x) == :(log(a) + log(b))
        @test gruntz_limit(:(log(-a*b) + 0*x), :x; signs = Dict(:a => :negative, :b => :positive)) == :(log(-1a) + log(b))
        @test gruntz_limit(:(log(a^2*x) - log(x)), :x; signs = neg) == :(2 * log(-1a))
        @test gruntz_limit(:(sqrt(a*b)*x), :x; signs = nn) == Inf
        @test_throws GruntzError gruntz_limit(:(log(a*b*x)/x), :x; signs = Dict(:a => :negative, :b => :positive))
    end

    @testset "cases of parameters (experimental)" begin
        shown(cs) = Set((isempty(conds) ? "always" : join(string.(conds), " && ")) =>
                        (v isa Expr ? string(v) : v) for (conds, v) in cs)
        @test shown(gruntz_cases(:(x^(a - 2)), :x)) == Set(["a < 2" => 0, "a == 2" => 1, "a > 2" => Inf])
        @test shown(gruntz_cases(:(x^a * log(x)), :x, 0)) == Set(["a <= 0" => -Inf, "a > 0" => 0])
        @test shown(gruntz_cases(:(a^x), :x)) ==
              Set(["a <= 0" => :undefined, "a > 0 && a < 1" => 0, "a == 1" => 1, "a > 1" => Inf])
        @test shown(gruntz_cases(:(1/(x - a)), :x, 0; dir = :both)) ==
              Set(["a != 0" => "-1 * a ^ -1", "a == 0" => :nolimit])
        @test shown(gruntz_cases(:((x^a + 1)^(1/log(x))), :x)) == Set(["a <= 0" => 1, "a > 0" => "exp(a)"])
        @test shown(gruntz_cases(:(sqrt(x^2 + a*x) - b*x), :x)) ==
              Set(["b < 1" => Inf, "b == 1" => "1//2 * a", "b > 1" => -Inf])
        @test shown(gruntz_cases(:(sin(a*x)/sin(b*x)), :x, 0; dir = :both)) ==
              Set(["b != 0" => "a * b ^ -1", "b == 0" => :undefined])
        @test shown(gruntz_cases(:(abs(x)/x), :x, :a; dir = :both)) ==
              Set(["a < 0" => -1, "a == 0" => :nolimit, "a > 0" => 1])
        # a negative coefficient with a parameter: the split is on the parameter's sign
        @test shown(gruntz_cases(:(log(-a*x)/x), :x)) == Set(["a < 0" => 0, "a >= 0" => :undefined])
        @test shown(gruntz_cases(:(log(-a*x)*x), :x, 0)) == Set(["a < 0" => 0, "a >= 0" => :undefined])
        @test shown(gruntz_cases(:(log(-a*x)*x), :x, 0; dir = :-)) == Set(["a <= 0" => :undefined, "a > 0" => 0])
        @test shown(gruntz_cases(:(log(a*x)*x), :x, 0; dir = :-)) == Set(["a < 0" => 0, "a >= 0" => :undefined])
        @test shown(gruntz_cases(:(log(-a*x)/x), :x, -Inf)) == Set(["a <= 0" => :undefined, "a > 0" => 0])
        @test shown(gruntz_cases(:(log(-a)*x), :x)) ==
              Set(["a < -1" => Inf, "a == -1" => 0, "a < 0 && a > -1" => -Inf, "a >= 0" => :undefined])
        @test shown(gruntz_cases(:(sqrt(-a*x)/x), :x)) == Set(["a <= 0" => 0, "a > 0" => :undefined])
        # a fractional power of a parameter needs a nonnegative base (positive, for a
        # negative exponent), and is then positive
        @test shown(gruntz_cases(:(sqrt(a)*x), :x)) == Set(["a < 0" => :undefined, "a == 0" => 0, "a > 0" => Inf])
        @test shown(gruntz_cases(:(a^(1//3)*x), :x)) == Set(["a < 0" => :undefined, "a == 0" => 0, "a > 0" => Inf])
        @test shown(gruntz_cases(:(x/sqrt(a)), :x)) == Set(["a <= 0" => :undefined, "a > 0" => Inf])
        @test shown(gruntz_cases(:(sqrt(a - 1)*x), :x)) == Set(["a < 1" => :undefined, "a == 1" => 0, "a > 1" => Inf])
        @test shown(gruntz_cases(:(sqrt(a)*x + x), :x)) == Set(["a < 0" => :undefined, "a >= 0" => Inf])
        @test shown(gruntz_cases(:(sqrt(a*x)/x), :x)) == Set(["a < 0" => :undefined, "a >= 0" => 0])
        @test shown(gruntz_cases(:(sqrt(a*x)*x), :x, 0; dir = :-)) == Set(["a <= 0" => 0, "a > 0" => :undefined])
        @test gruntz_limit(:(sqrt(a)*x + x), :x) == Inf
        @test gruntz_limit(:(log(-2a*x)/x), :x; signs = Dict(:a => :negative)) == 0
        @test gruntz_limit(:(sqrt(-a*x)/x), :x; signs = Dict(:a => :negative)) == 0
        @test_throws GruntzError gruntz_limit(:(log(-a*x)/x), :x; signs = Dict(:a => :positive))
        # a product of parameters: valid when both are negative
        @test shown(gruntz_cases(:(sqrt(a*b)*x), :x)) ==
              Set(["a < 0 && b < 0" => Inf, "a < 0 && b == 0" => 0, "a < 0 && b > 0" => :undefined, "a == 0" => 0,
                   "a > 0 && b < 0" => :undefined, "a > 0 && b == 0" => 0, "a > 0 && b > 0" => Inf])
        cs = gruntz_cases(:(log(a*b)*x), :x)
        @test cs(:a => -2, :b => -1//2) == 0 && cs(:a => -2, :b => -1) == Inf && cs(:a => -2, :b => -1//4) == -Inf
        @test cs(:a => 2, :b => 1//2) == 0 && cs(:a => -2, :b => 1) == :undefined
        @test shown(gruntz_cases(:(log(-a) - 1 + 0*x), :x)) == Set(["a < 0" => "-1 + log(-1a)", "a >= 0" => :undefined])
        # signs restrict the cases; a limit without parameters has one case
        @test shown(gruntz_cases(:(x^(a - 2)), :x; signs = Dict(:a => :negative))) == Set(["always" => 0])
        @test shown(gruntz_cases(:(sin(x)/x), :x, 0)) == Set(["always" => 1])
        @test shown(gruntz_cases(:(x^a), :x; signs = Dict(:a => :nonnegative))) == Set(["a == 0" => 1, "a > 0" => Inf])
        @test shown(gruntz_cases(:(x^a), :x; signs = Dict(:a => :nonzero))) == Set(["a < 0" => 0, "a > 0" => Inf])
        @test shown(gruntz_cases(:(x^a), :x; signs = Dict(:a => :nonpositive))) == Set(["a < 0" => 0, "a == 0" => 1])
        # looking up a case by the values of the parameters
        cs = gruntz_cases(:((a^x + b^x)^(1/x)), :x)
        @test cs(:a => 2, :b => 3) == 3 && cs(:a => 3, :b => 2) == 3 && cs(:a => 1//2, :b => 1//4) == 1//2
        @test cs(Dict(:a => -1, :b => 2)) == :undefined
        @test cs[:a => 2, :b => 3].second == :b
        @test cs[:a => 2, :b => 3] in cs
        @test cs[Dict(:a => 3, :b => 2)].second == :a
        @test_throws ArgumentError cs(:a => 2)                       # b is needed
        cs = gruntz_cases(:(x^(a - 2)), :x; signs = Dict(:a => :negative))
        @test cs(:a => -1) == 0
        @test_throws ArgumentError cs(:a => 1)                       # outside the signs
        cs = gruntz_cases(:(x^(a - 2)), :x)
        @test cs[end].second == Inf
        @test length(filter(p -> p.second == 0, cs)) == 1
        # bounded oscillation in a case
        @test shown(gruntz_cases(:(x^a * sin(1/x)), :x, 0)) == Set(["a <= 0" => :nolimit, "a > 0" => 0])
        @test shown(gruntz_cases(:(x^a * sin(x)), :x)) == Set(["a < 0" => 0, "a >= 0" => :nolimit])
        # a GruntzError for a case that could not be computed: x^a -> oo, 1 - cos(1/x) touches 0
        cs = gruntz_cases(:(x^a * (1 - cos(1/x))), :x, 0)
        @test cs(:a => -1) isa GruntzError && cs(:a => 0) == :nolimit && cs(:a => 1) == 0
    end

    @testset "bounded oscillation" begin
        nolimit(f, args...; kw...) = try
            gruntz_limit(f, args...; kw...); false
        catch err
            err isa GruntzError && err.kind === :nolimit
        end
        failed(f, args...; kw...) = try
            gruntz_limit(f, args...; kw...); false
        catch err
            err isa GruntzError && err.kind === :fail
        end
        # bounded × (-> 0), bounded + (-> ±oo), (-> ±oo) × (bounded, of one sign)
        @test gruntz_limit(:(sin(x)/x), :x) == 0
        @test gruntz_limit(:(sin(x)/x), :x, -Inf) == 0
        @test gruntz_limit(:((1 - cos(x))/x^2), :x) == 0
        @test gruntz_limit(:(sin(x) + x), :x) == Inf
        @test gruntz_limit(:(x*(2 + sin(x))), :x) == Inf
        @test gruntz_limit(:(-x*(2 + sin(x))), :x) == -Inf
        @test gruntz_limit(:(exp(-x)*sin(exp(x))), :x) == 0
        @test gruntz_limit(:(cos(x)/x + 3), :x) == 3
        @test gruntz_limit(:(sin(sin(x))/x), :x) == 0
        @test gruntz_limit(:(sin(x + exp(-x))/x), :x) == 0
        @test gruntz_limit(:(sin(a*x)/x), :x) == 0
        @test gruntz_limit(:(sqrt(1 - cos(x))/x), :x) == 0
        # a dominant term with a bounded one: x + 2cos(x) ~ x
        @test gruntz_limit(:(2*exp(-sin(x))/(x + 2*cos(x))), :x) == 0
        @test gruntz_limit(:(x/(x + 2cos(x))), :x) == 1
        @test gruntz_limit(:((x + sin(x))/(x - cos(x))), :x) == 1
        @test gruntz_limit(:(x^2 + x*sin(x)), :x) == Inf
        @test gruntz_limit(:(log(2 + sin(x))/x), :x) == 0
        @test gruntz_limit(:(log(x + sin(x))/log(x)), :x) == 1
        # at finite points
        @test gruntz_limit(:((h/2 + h^2*sin(π/h))/h), :h, 0; dir = :both) == 1//2
        @test gruntz_limit(:(x^2*sin(1/x)/x), :x, 0; dir = :both) == 0
        # no limit
        @test nolimit(:(sin(x)), :x)
        @test nolimit(:(x*sin(x)), :x)
        @test nolimit(:(exp(sin(x))), :x)
        @test nolimit(:(sin(1/x)), :x, 0)
        @test nolimit(:(sin(1/x)/x), :x, 0)
        # Gruntz's counterexample to l'Hôpital's rule: the ratio is exp(-sin(x))
        @test nolimit(:((sin(2x)/2 + x)/(exp(sin(x))*(cos(x)*sin(x) + x))), :x)
        # undecided: an error, never a wrong answer
        @test failed(:(tan(x)), :x)
        @test failed(:(1/sin(x)), :x)
        @test failed(:(sin(x)^2 + cos(x)^2), :x)                # sin and cos taken as independent
        @test failed(:(x*(1 - cos(x)) + sqrt(x)), :x)           # -> oo: 1 - cos(x) only touches 0
        @test failed(:(x + x*sin(x)), :x)
        @test failed(:(exp(x*sin(x))), :x)
    end

    @testset "gamma and factorial" begin
        # x^x/x!, c^x/x!, and ratio tests a(n+1)/a(n)
        @test gruntz_limit(:(x^x/factorial(x)), :x) == Inf
        @test gruntz_limit(:(x^x/gamma(x + 1)), :x) == Inf
        @test gruntz_limit(:((1 + a)^x/factorial(x)), :x; signs = Dict(:a => :positive)) == 0
        @test gruntz_limit(:(factorial(x + 1)/factorial(x)/(x + 1)), :x) == 1
        @test eval(gruntz_limit(:((factorial(x + 1)/(x + 1)^(x + 1))/(factorial(x)/x^x)), :x)) ≈ exp(-1)
        @test gruntz_limit(:((a^(2x + 3)/factorial(2x + 3))/(a^(2x + 1)/factorial(2x + 1))), :x) == 0
        # Stirling's formula, and its next term
        @test gruntz_limit(:(factorial(x)/(sqrt(2*π*x)*(x/ℯ)^x)), :x) == 1
        @test gruntz_limit(:(x*(factorial(x)/(sqrt(2*π*x)*(x/ℯ)^x) - 1)), :x) == 1//12
        @test eval(gruntz_limit(:(gamma(x)*exp(x)/x^(x - 1//2)), :x)) ≈ sqrt(2π)
        @test eval(gruntz_limit(:(loggamma(x) - (x - 1//2)*log(x) + x), :x)) ≈ log(2π)/2
        @test gruntz_limit(:(log(gamma(x))/(x*log(x))), :x) == 1
        @test gruntz_limit(:(gamma(x + 1//2)/(gamma(x)*sqrt(x))), :x) == 1
        @test gruntz_limit(:(gamma(x)/gamma(x + 1//3)*x^(1//3)), :x) == 1
        @test gruntz_limit(:(gamma(log(x))/x), :x) == Inf
        @test gruntz_limit(:(exp(x)/gamma(x)), :x) == 0
        @test gruntz_limit(:(factorial(x)/exp(x^2)), :x) == 0
        @test gruntz_limit(:(sin(x)/factorial(x)), :x) == 0
        @test gruntz_limit(:(x*gamma(1/x)), :x, 0; dir = :+) == Inf
        # constant arguments
        @test gruntz_limit(:(factorial(5) + 1/x), :x) == 120
        @test_throws GruntzError gruntz_limit(:(gamma(0) + x), :x, 1)
        # not supported: an argument with a finite limit, or one that tends to -oo
        @test_throws GruntzError gruntz_limit(:(gamma(x)), :x, 2)
        @test_throws GruntzError gruntz_limit(:(gamma(-x)), :x)
    end

    @testset "sinint, cosint and erfi" begin
        nolimit(f, args...) = try
            gruntz_limit(f, args...); false
        catch err
            err isa GruntzError && err.kind === :nolimit
        end
        @test eval(gruntz_limit(:(sinint(x)), :x)) ≈ π/2
        @test eval(gruntz_limit(:(sinint(x)), :x, -Inf)) ≈ -π/2
        @test eval(gruntz_limit(:(sinint(-x)), :x)) ≈ -π/2
        @test eval(gruntz_limit(:(sinint(2x + 1)), :x)) ≈ π/2
        @test eval(gruntz_limit(:(sinint(1/x)), :x, 0; dir = :+)) ≈ π/2
        @test eval(gruntz_limit(:(sinint(log(x))), :x)) ≈ π/2
        @test eval(gruntz_limit(:(sinint(exp(x))), :x)) ≈ π/2
        @test gruntz_limit(:(sinint(x) - sinint(x + 1)), :x) == 0
        @test gruntz_limit(:(sinint(x)/x), :x) == 0
        @test gruntz_limit(:(cosint(x)), :x) == 0
        @test gruntz_limit(:(cosint(x)*log(x)), :x) == 0
        # the remainders oscillate: π/2 - sinint(x) ~ cos(x)/x, cosint(x) ~ sin(x)/x
        @test nolimit(:(x*(π/2 - sinint(x))), :x)
        @test nolimit(:(x*cosint(x)), :x)
        @test nolimit(:(x^2*(π/2 - sinint(x) - cos(x)/x)), :x)     # ~ sin(x)
        # erfi(x) ~ exp(x^2)/(x sqrt(π))
        @test gruntz_limit(:(erfi(x)), :x) == Inf
        @test gruntz_limit(:(erfi(x)), :x, -Inf) == -Inf
        @test eval(gruntz_limit(:(erfi(x)*x*exp(-x^2)), :x)) ≈ 1/sqrt(π)
        @test gruntz_limit(:(erfi(x)/exp(x^2)), :x) == 0
        # constants; cosint of a negative number is complex, and has a singularity at 0
        @test gruntz_limit(:(sinint(2) + 1/x), :x) == :(sinint(2))
        @test_throws GruntzError gruntz_limit(:(cosint(x)), :x, -Inf)
        @test_throws GruntzError gruntz_limit(:(cosint(0) + x), :x, 1)
        @test_throws GruntzError gruntz_limit(:(cosint(x)), :x, 0; dir = :-)
        @test_throws GruntzError gruntz_limit(:(cosint(x)), :x, -1)
        # at finite points, by Taylor's series
        @test gruntz_limit(:(sinint(x)), :x, 0) == 0
        @test gruntz_limit(:(sinint(x)/x), :x, 0; dir = :both) == 1
        @test gruntz_limit(:((sinint(x) - x)/x^3), :x, 0; dir = :both) == -1//18
        @test gruntz_limit(:(sinint(sin(x))/x), :x, 0; dir = :both) == 1
        @test gruntz_limit(:(sinint(a*x)/x), :x, 0; dir = :both) == :a
        @test gruntz_limit(:(sinint(x)), :x, 1) == :(sinint(1))
        @test eval(gruntz_limit(:((sinint(x) - sinint(1))/(x - 1)), :x, 1; dir = :both)) ≈ sin(1)
        @test eval(gruntz_limit(:((sinint(x) - sinint(1) - sin(1)*(x - 1))/(x - 1)^2), :x, 1; dir = :both)) ≈
              (cos(1) - sin(1))/2
        @test eval(gruntz_limit(:(cosint(x) - log(x)), :x, 0)) ≈ Base.MathConstants.eulergamma
        @test gruntz_limit(:((cosint(x) - log(x) - $(Base.MathConstants.eulergamma))/x^2), :x, 0) == -1//4
        @test gruntz_limit(:(cosint(x)), :x, 0) == -Inf
        @test gruntz_limit(:(x*cosint(x)), :x, 0) == 0
        @test eval(gruntz_limit(:((cosint(x) - cosint(2))/(x - 2)), :x, 2; dir = :both)) ≈ cos(2)/2
        @test eval(gruntz_limit(:(erfi(x)/x), :x, 0; dir = :both)) ≈ 2/sqrt(π)
        @test eval(gruntz_limit(:((erfi(x) - 2x/sqrt(π))/x^3), :x, 0; dir = :both)) ≈ 2/(3sqrt(π))
        @test eval(gruntz_limit(:((erfi(x) - erfi(1))/(x - 1)), :x, 1; dir = :both)) ≈ 2ℯ/sqrt(π)
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

    @testset "negative arguments that are positive where the limit is taken" begin
        # -x > 0 for x -> 0⁻ and x -> -Inf: the domain check waits for the substitution
        @test gruntz_limit(:(x*log(-x)), :x, 0; dir = :-) == 0
        @test gruntz_limit(:(log(-x)), :x, 0; dir = :-) == -Inf
        @test gruntz_limit(:(sqrt(-x)), :x, 0; dir = :-) == 0
        @test gruntz_limit(:((-x)^(1//3)*x), :x, 0; dir = :-) == 0
        @test gruntz_limit(:(log(-x)/x), :x, -Inf) == 0
        @test gruntz_limit(:(sqrt(-x)/x), :x, -Inf) == 0
        # and still undefined where the argument is negative
        @test_throws GruntzError gruntz_limit(:(log(-x)), :x)
        @test_throws GruntzError gruntz_limit(:(sqrt(-x)), :x)
        @test_throws GruntzError gruntz_limit(:(log(-x)), :x, 0)
        @test_throws GruntzError gruntz_limit(:(log(-x)), :x, 0; dir = :both)
        @test_throws GruntzError gruntz_limit(:(x*log(-x)), :x, 1; dir = :-)
        @test_throws GruntzError gruntz_limit(:(log(-2)*x), :x)
    end

    @testset "errors" begin
        @test_throws GruntzError gruntz_limit(:(sin(x)), :x)
        @test_throws GruntzError gruntz_limit(:(sin(1/x)), :x, 0)
        @test_throws GruntzError gruntz_limit(:(zeta(x)), :x)
        @test_throws GruntzError gruntz_limit(:(log(x)), :x, -1)
        @test_throws GruntzError gruntz_limit(:(sqrt(-1 - x^2)), :x)
        @test_throws GruntzError gruntz_limit(:(1/x), :x, 0; dir = :sideways)
    end
end
