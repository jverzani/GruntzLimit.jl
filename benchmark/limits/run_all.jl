# julia run_all.jl [LIMIT]
# Runs the methods one after another (a cold start each) with a limit of
# LIMIT seconds per problem (default 60), then builds the page.
const HERE = @__DIR__
const LIMIT = get(ARGS, 1, "60")
mkpath(joinpath(HERE, "results"))

# the git commit of GruntzLimit, and whether it has uncommitted changes (other
# than this run's results, which the run rewrites). Found before anything is written.
function commit(dir)
    try
        c = readchomp(`git -C $dir rev-parse --short HEAD`)
        changes = readchomp(`git -C $dir status --porcelain --untracked-files=no -- . ':(exclude)benchmark/limits/results'`)
        c * (isempty(changes) ? "" : " (with uncommitted changes)")
    catch
        "unknown"
    end
end
commits = [("GruntzLimit", commit(joinpath(HERE, "..", "..")))]
open(joinpath(HERE, "results", "commits.tsv"), "w") do io
    foreach(((name, c),) -> println(io, name, "\t", c), commits)
end

for (name, env) in (("expr", "env_gruntz"), ("symengine", "env_gruntz"), ("symbolicutils", "env_gruntz"),
                    ("symboliclimits", "env_sl"), ("symboliclimits_explog", "env_sl"))
    @info "running $name"
    run(`julia $(joinpath(HERE, "supervise.jl")) $name $env $LIMIT`)
end
run(`julia $(joinpath(HERE, "build.jl"))`)
