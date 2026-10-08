using GruntzLimit
using Test

@testset "Expressions" begin
    @test gruntz_limit(:(sin(x)/x),:x, 0) == 1
    @test gruntz_limit(:(atan(x)), :x, Inf) ≈ pi/2
    @test gruntz_limit(:(log(x + 1) - log(x)), :x, Inf) == 0
    @test gruntz_limit(:(x/abs(x)), :x, 0; dir=:+) == 1
    @test gruntz_limit(:(x/abs(x)), :x, 0; dir=:-) == -1
end

include("test_SymEngine.jl")
include("test_SimpleExpressions.jl")
