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
end
