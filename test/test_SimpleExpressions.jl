import SimpleExpressions
SimpleExpressions.@symbolic_variables x a b
ONE, PI = one(x), π * one(x)

@testset "SimpleExpressions" begin
    include("test_limit.jl")

    # answers are unevaluated expressions; calling one evaluates it
    @test gruntz_limit(atan(x), x)() ≈ π/2
    @test gruntz_limit(asin(x), x, 1//2)() ≈ π/6
    @test gruntz_limit(acos(x), x, 1//2)() ≈ π/3

    # complex values
    @test gruntz_limit(exp(-(2 + 3im)*x), x) == 0
    @test gruntz_limit((exp(im*x) - 1)/x, x, 0) == im
    @test gruntz_limit(sqrt(2 + im*x), x, 0)() ≈ sqrt(2)

    # abs of a power of a negative quantity (SymPy #25681, #26513)
    @test gruntz_limit(x/abs(sqrt(x^2 - 1)), x, -1; dir = :+) == -Inf
    @test gruntz_limit(x/abs(sqrt(x^2 - 1)), x, 1; dir = :-) == Inf
    @test_throws GruntzError gruntz_limit((-x/(x + 1))^x, x)
    @test gruntz_limit(abs(cos(x)*exp(-x)), x) == 0
end
