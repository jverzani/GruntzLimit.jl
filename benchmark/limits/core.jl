# Shared by the workers. Before including, a worker defines:
#   VAR::Dict{Symbol,Any}    the variable x, the parameters a, b, and the constants π, ℯ
#   LIMIT(f, x, x0, dir)     the method being compared; dir is :+, :- or :both
#   SOLVED(out)::Bool        did it return a limit (and not, say, an unevaluated term)?
#   EVAL(out, vals)          the value of `out` with each parameter `v` replaced by
#                            `vals[v]`, as a number, or `nothing`
#   BUILD(ex)                (optional) the term from the problem's expression;
#                            by default the expression evaluated with VAR's values
#   NOTE()                   (optional) a string appended to the recorded answer
# Usage: julia --project=ENV worker_X.jl START OUTFILE (run by supervise.jl)
const T_LOADED = time()

const PROBLEMS = include(joinpath(@__DIR__, "problems.jl"))
const ALLVARS = (:x, :a, :b, :π, :ℯ)

function build(ex)
    m = Module()
    for v in ALLVARS
        Core.eval(m, :(const $v = $(VAR[v])))
    end
    Core.eval(m, ex)
end
isdefined(@__MODULE__, :BUILD) || (BUILD(ex) = build(ex))
isdefined(@__MODULE__, :NOTE) || (NOTE() = "")
# the limit point: ±Inf as is, anything else built like the expression
point(x0) = x0 isa Real && isinf(x0) ? x0 : BUILD(x0)

# ---- check: the answer's value, parameters fixed, against the reference answer
const PARAMS = Dict(:a => 1.7, :b => 2.3)
function reference(ans)
    m = Module()
    Core.eval(m, :(a = $(PARAMS[:a]); b = $(PARAMS[:b])))
    Float64(Core.eval(m, ans))
end

function check(out, ans)
    occursin("NaN", string(out)) && return :wrong   # e.g. SymEngine's exp(NaN*log(…))
    u = out isa Real ? out : EVAL(out, PARAMS)
    u === nothing && return :unverified
    u = complex(u)
    abs(imag(u)) <= 1e-8 * max(1, abs(u)) || return :wrong
    v, r = real(u), reference(ans)
    isinf(r) ? (v == r ? :verified : :wrong) :
        isfinite(v) && abs(v - r) <= 1e-8 * max(1, abs(r)) ? :verified : :wrong
end

clean(s) = replace(s, r"\s+" => " ")[1:min(end, 400)]

function run_one(io, i)
    ex, x0, dir, ans, _ = PROBLEMS[i]
    println(io, "S\t$i\t", time()); flush(io)
    f = BUILD(ex)
    x = VAR[:x]
    p = point(x0)
    t0 = time()
    out = try
        LIMIT(f, x, p, dir)
    catch err
        err
    end
    dt = time() - t0
    if out isa Exception
        status, ver, s = :error, :none, sprint(showerror, out)
    elseif SOLVED(out)
        status, s = :solved, string(out) * NOTE()
        ver = try check(out, ans) catch; :unverified end
    else
        status, ver, s = :unsolved, :none, string(out) * NOTE()
    end
    println(io, "R\t$i\t$status\t$ver\t$dt\t", clean(s)); flush(io)
    dt
end

let start = parse(Int, ARGS[1]), outfile = ARGS[2]
    open(outfile, "a") do io
        println(io, "L\t", T_LOADED - T_START, "\t", start); flush(io)
        start == 1 && for (k, m) in Base.loaded_modules
            k.name in ("GruntzLimit", "SymbolicLimits", "SymbolicUtils", "SymEngine", "SymJ", "Giac") || continue
            println(io, "V\t", k.name, "\t", pkgversion(m))
        end
        foreach(i -> run_one(io, i), start:length(PROBLEMS))
        println(io, "D"); flush(io)
    end
end
