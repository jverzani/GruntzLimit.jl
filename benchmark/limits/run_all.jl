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
# SymJ is not registered yet: env_symj takes it from its main branch, updated here to
# the latest commit, which is recorded in place of a version
const SYMJ = "https://github.com/jverzani/SymJ.jl"
run(`julia --project=$(joinpath(HERE, "env_symj")) -e 'using Pkg; Pkg.update("SymJ")'`)
symj = try
    first(split(readchomp(`git ls-remote $SYMJ refs/heads/main`)))[1:7]
catch
    "unknown"
end
commits = [("GruntzLimit", commit(joinpath(HERE, "..", ".."))), ("SymJ", symj)]
open(joinpath(HERE, "results", "commits.tsv"), "w") do io
    foreach(((name, c),) -> println(io, name, "\t", c), commits)
end

for (name, env) in (("expr", "env_gruntz"), ("symengine", "env_gruntz"), ("symbolicutils", "env_gruntz"), ("symj", "env_symj"),
                    ("symboliclimits", "env_sl"), ("symboliclimits_explog", "env_sl"), ("giac", "env_giac"))
    @info "running $name"
    run(`julia $(joinpath(HERE, "supervise.jl")) $name $env $LIMIT`)
end
run(`julia $(joinpath(HERE, "build.jl"))`)
