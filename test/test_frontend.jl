import GruntzLimit: @limit, LimitCases

@testset "@limit" begin
    @test @limit(sin(x)/x, x => 0) == 1
    @test @limit(x^2 * exp(-x), x => Inf) == 0
    @test @limit(a + 1/x, x => Inf) == :a             # a parameter is a value
    @test @limit(x, x => 3) == 3
    # the default is two-sided
    @test_throws GruntzError @limit(1/x, x => 0)
    for d in (:+, "+", '+', +)
        @test @limit(1/x, x => 0, d) == Inf
        @test @limit(1/x, x => 0, dir = d) == Inf
    end
    for d in (:-, "-", '-', -)
        @test @limit(1/x, x => 0, d) == -Inf
    end
    @test @limit(abs(x), x => 0, "both") == 0
    @test_throws ArgumentError @limit(1/x, x => 0, :right)
    @test_throws ArgumentError @limit(1/x, x => 0, dir = "left")
    # a limit that does not exist, or a function not defined, throws
    @test_throws GruntzError @limit(sin(x), x => Inf)
    @test_throws GruntzError @limit(log(x)*x, x => 0)
    @test @limit(log(x)*x, x => 0, :+) == 0
    try
        @limit(1/x, x => 0)
    catch err
        @test err isa GruntzError && err.kind === :nolimit
    end
    # cases, unless `signs` decide them
    cs = @limit(x^a, x => Inf)
    @test cs isa LimitCases && length(cs) == 3
    @test @limit(x^a, x => Inf, signs = Dict(:a => :positive)) == Inf
    @test @limit(x^(a - 2), x => Inf, signs = Dict(:a => :negative)) == 0
    @test @limit(x^a, x => Inf, +, signs = Dict(:a => :negative)) == 0
    # names in the expression are parameters; the point is evaluated, and `$v` too
    p = 2
    @test @limit(p*x, x => 1) == :p
    @test @limit(x^2, x => p) == 4
    @test @limit(sin($p*x)/x, x => 0) == 2
    f(q) = @limit(sin($q*x)/x, x => 0)
    @test f(3) == 3
    # malformed calls fail when the macro is expanded
    @test_throws ArgumentError @macroexpand @limit(x, x)
    @test_throws ArgumentError @macroexpand @limit(x, 2x => 0)
    @test_throws ArgumentError @macroexpand @limit(x, x => 0, +, -)
end
