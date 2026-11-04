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
end
