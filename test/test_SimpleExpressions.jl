import SimpleExpressions
SimpleExpressions.@symbolic_variables x a b
ONE, PI = one(x), π * one(x)

@testset "SimpleExpressions" begin
    include("test_limit.jl")

    # answers are unevaluated expressions; calling one evaluates it
    @test gruntz_limit(atan(x), x)() ≈ π/2
    @test gruntz_limit(asin(x), x, 1//2)() ≈ π/6
    @test gruntz_limit(acos(x), x, 1//2)() ≈ π/3
end
