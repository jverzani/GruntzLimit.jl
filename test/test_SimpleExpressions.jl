import SimpleExpressions
using SimpleExpressions: simplify
SimpleExpressions.@symbolic_variables x a b



@testset "SimpleExpressions" begin
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
    @test gruntz_limit((1 + 1/x)^x, x) == exp(one(x))
    @test gruntz_limit((1 + a/x)^x, x) == exp(a)
end
