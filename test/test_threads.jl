@testset "concurrent limits" begin
    # Limits whose answers depend on the context (the signs given, the case being
    # computed), run concurrently: each task must see only its own context.
    # Meaningful with several threads (julia -t 4).
    problems = [
        () -> gruntz_limit(:(x^a), :x; signs = Dict(:a => :positive)) => Inf,
        () -> gruntz_limit(:(x^a), :x; signs = Dict(:a => :negative)) => 0,
        () -> gruntz_limit(:(exp(a*x) * x^2), :x; signs = Dict(:a => :negative)) => 0,
        () -> length(gruntz_cases(:(x^(a - 2)), :x)) => 3,
        () -> gruntz_limit(:(sin(x)/x), :x, 0) => 1,
    ]
    tasks = [Threads.@spawn(problems[mod1(i, length(problems))]()) for i in 1:200]
    @test all(t -> (p = fetch(t); p.first == p.second), tasks)
end
