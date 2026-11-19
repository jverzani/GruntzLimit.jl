import SymEngine
SymEngine.@vars x a b
ONE, PI = one(x), SymEngine.PI

@testset "SymEngine" begin
    include("test_limit.jl")

    # SymEngine simplifies these constant answers; they are built from atan
    @test gruntz_limit(asin(x), x, 1//2) == PI/6
    @test gruntz_limit(acos(x), x, 1//2) == PI/3

    # lambertw: SymEngine gives no operation for it; the result is built with its own
    W = SymEngine.lambertw
    @test gruntz_limit(exp(W(x)), x) == Inf
    @test gruntz_limit(W(x)/log(x), x) == 1
    @test gruntz_limit(W(x), x, 1) == W(ONE)

    # complex values: SymEngine's complex numbers and `IM`
    @test gruntz_limit(exp(-(2 + 3im)*x), x) == 0
    @test gruntz_limit(sqrt(2 + im*x), x, 0) == sqrt(2*ONE)
    @test gruntz_limit(exp(-(2 + 3im)*x)/(-(2 + 3im)), x, 0) == -2//13 + 3//13*im

    # sqrt(u^2) = |u| (SymPy #27551)
    @test gruntz_limit(sqrt(log(x)^2)/log(x), x, 1; dir = :-) == -1
    @test gruntz_limit(1/(x*sqrt(log(x)^2)), x, 1; dir = :-) == Inf
    @test gruntz_limit(sqrt(log(x)^2)/log(x), x, 1//2) == -1

    # abs of a power of a negative quantity (SymPy #25681, #26513)
    @test gruntz_limit(x/abs(sqrt(x^2 - 1)), x, -1; dir = :+) == -Inf
    @test gruntz_limit(x/abs(sqrt(x^2 - 1)), x, 1; dir = :-) == Inf
    @test_throws GruntzError gruntz_limit((-x/(x + 1))^x, x)
    @test gruntz_limit(abs(cos(x)*exp(-x)), x) == 0

    # a complex base (SymPy #23915)
    @test gruntz_limit((1//10 + SymEngine.IM/10)^x, x) == 0

    # atan of an argument tending to ±i written with real radicals, sqrt(b)/sqrt(-b): a
    # GruntzError, not a division by zero in GMP (SymJ's ∫₀^π 2/(1 - a²cos²x) dx)
    c = sqrt(a^2 - 1)/sqrt(1 - a^2)
    @test_throws "tends to ±i" gruntz_limit(atan(x + c), x, 0)
    # given a > 1, sqrt(1 - a^2) is undefined first (a polynomial in a decided on a > 1)
    @test_throws "not positive" gruntz_limit(atan(x + c), x, 0; dir = :-, signs = [a - 1 => :positive])
    @test_throws "not positive" gruntz_limit(atan(tan(x)/sqrt(1 - a^2)), x, acos(1/a); dir = :-,
                                             signs = [a - 1 => :positive])
    @test gruntz_limit(1/(x + 1 + c^2), x, 0; dir = :+, signs = [a - 1 => :positive]) == Inf

    # the sign of a polynomial in one parameter on its interval (Sturm): a radicand
    # 1 - a^2 < 0 for a > 1 is undefined, and polynomial coefficients have known signs
    @test_throws "not nonnegative" gruntz_limit(sqrt(1 - a^2), x, 0; signs = [a - 1 => :positive])
    @test_throws "not nonnegative" gruntz_limit(x*sqrt(1 - a^2), x; signs = [a - 1 => :positive])
    @test gruntz_limit(x*sqrt(a^2 - 1), x; signs = [a - 1 => :positive]) == Inf
    @test gruntz_limit((a^2 - 3a + 2)*x, x; signs = [a - 1 => :positive, a - 2 => :negative]) == -Inf
    @test gruntz_limit((a^2 - 3a + 2)*x, x; signs = [a - 2 => :positive]) == Inf
    @test gruntz_limit(x^(1 - a^2), x; signs = [a + 1 => :negative]) == 0
    @test gruntz_limit(x^(a^3 - 2), x; signs = [a - 2 => :positive]) == Inf
    @test gruntz_limit(x^(a^2 - 2a + 1), x; signs = [a - 1 => :positive]) == Inf
    # a root inside the interval: undecided, so the generic answer
    @test gruntz_limit(x*sqrt(a^2 - 4), x; signs = [a => :positive]) == Inf
end
