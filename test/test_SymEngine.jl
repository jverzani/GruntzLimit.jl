import SymEngine
SymEngine.@vars x a b
ONE, PI = one(x), SymEngine.PI

@testset "SymEngine" begin
    include("test_limit.jl")

    # SymEngine simplifies these constant answers; they are built from atan
    @test gruntz_limit(asin(x), x, 1//2) == PI/6
    @test gruntz_limit(acos(x), x, 1//2) == PI/3
end
