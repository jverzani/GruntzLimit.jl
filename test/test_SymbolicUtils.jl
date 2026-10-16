# SymbolicUtils.jl terms. Numbers in its expressions are constant nodes (not
# Julia numbers) and π is wrapped as identity(π); answers that are not rational
# are built as SymbolicUtils terms with `maketerm`, so they stay exact.
import SymbolicUtils
using SymbolicUtils: @syms
@syms x::Real a::Real b::Real
# SymbolicUtils folds `π` and `one(x)` to plain numbers (e.g. `atan(x) - π` becomes
# `atan(x) - 3.14159…`); exact constants are a `Const` and identity(π), which is
# how it represents π in `π*x`
ONE = SymbolicUtils.Const{SymbolicUtils.SymReal}(1)
PI = SymbolicUtils.maketerm(typeof(x), identity, Any[π], nothing)

@testset "SymbolicUtils" begin
    include("test_limit.jl")

    T = typeof(x)
    # numeric value of an answer, binding the parameters `a` and `b`
    su(r; a0 = 2.0, b0 = 3.0) = Float64(SymbolicUtils.unwrap_const(
        SymbolicUtils.substitute(r, Dict(a => a0, b => b0); fold = Val(true))))
    # an exact SymbolicUtils term: no floating point constants
    exact(r) = r isa T && !occursin(r"\d\.\d", string(r))

    @testset "exact answers" begin
        # not simplified to π/6, π/3 as SymEngine does, but exact
        for (f, val) in [(asin(x), π/6), (acos(x), π/3)]
            r = gruntz_limit(f, x, 1//2)
            @test exact(r) && su(r) ≈ val
        end
        @test gruntz_limit(x * (2atan(x) - PI), x) == -2
        @test gruntz_limit(x * (atan(x) - PI/2), x) == -1
        @test gruntz_limit(exp(π*x), x) == Inf
        @test gruntz_limit(x^ℯ / exp(x), x) == 0
        @test isequal(gruntz_limit(π*x/x, x, 0), PI)
    end

    @testset "parameters" begin
        for (f, x0, val) in [(sqrt(x^2 + a*x) - x, Inf, 1),
                             (sin(a*x)/x, 0, 2),
                             (x^2 + a*x, a, 8),
                             (exp(x)/x, b, exp(3)/3),
                             (x^2, a + 1, 9)]
            r = gruntz_limit(f, x, x0)
            @test exact(r) && su(r) ≈ val
        end
    end

    @testset "errors" begin
        @test_throws GruntzError gruntz_limit(sin(1/x), x, 0)
        @test_throws GruntzError gruntz_limit(asin(x), x, 1; dir = :+)
    end
end
