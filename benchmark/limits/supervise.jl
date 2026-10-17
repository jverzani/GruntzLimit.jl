# julia supervise.jl NAME ENV LIMIT
# Runs worker_NAME.jl in the environment ENV (a folder here), restarting it
# after a problem takes more than LIMIT seconds or the process dies.
# Results go to results/results_NAME.tsv; see README.md for the format.
const NAME, ENVDIR, LIMIT = ARGS[1], joinpath(@__DIR__, ARGS[2]), parse(Float64, ARGS[3])
const N = length(include(joinpath(@__DIR__, "problems.jl")))
const RESULTS = joinpath(@__DIR__, "results")
outfile = joinpath(RESULTS, "results_$NAME.tsv")
for f in (outfile, joinpath(RESULTS, "stdout_$NAME.log"), joinpath(RESULTS, "stderr_$NAME.log"))
    rm(f; force = true)
end
t_wall = time()
start = 1
while start <= N
    global start
    cmd = `julia --project=$ENVDIR $(joinpath(@__DIR__, "worker_$NAME.jl")) $start $outfile`
    proc = run(pipeline(cmd; stdout = joinpath(RESULTS, "stdout_$NAME.log"), stderr = joinpath(RESULTS, "stderr_$NAME.log"), append = true); wait = false)
    while true
        sleep(0.5)
        lines = isfile(outfile) ? readlines(outfile) : String[]
        last_s = findlast(l -> startswith(l, "S\t"), lines)
        last_r = findlast(l -> startswith(l, "R\t"), lines)
        done = any(==("D"), lines) && process_exited(proc)
        done && (start = N + 1; break)
        current = (last_s !== nothing && (last_r === nothing || last_r < last_s)) ?
            split(lines[last_s], '\t') : nothing
        if current !== nothing && time() - parse(Float64, current[3]) > LIMIT
            kill(proc); wait(proc)
            i = parse(Int, current[2])
            open(io -> println(io, "R\t$i\ttimeout\tnone\t$LIMIT\t"), outfile, "a")
            start = i + 1
            break
        elseif process_exited(proc)
            if current !== nothing   # crashed during a problem
                i = parse(Int, current[2])
                open(io -> println(io, "R\t$i\tcrash\tnone\t0\t"), outfile, "a")
                start = i + 1
            else
                start = N + 1
            end
            break
        end
    end
end
open(io -> println(io, "T\t", time() - t_wall, "\t", LIMIT), outfile, "a")
