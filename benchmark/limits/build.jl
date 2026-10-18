# julia build.jl
# Builds results/limits_comparison.html from results/*.tsv and template.html
const HERE = @__DIR__
const RESULTS = joinpath(HERE, "results")
const METHODS = [
    ("expr", "GruntzLimit", "Gruntz", "Expr"),
    ("symengine", "GruntzLimit", "Gruntz", "SymEngine"),
    ("symbolicutils", "GruntzLimit", "Gruntz", "SymbolicUtils"),
    ("symboliclimits", "SymbolicLimits", "limit", "SymbolicUtils"),
    ("symboliclimits_explog", "SymbolicLimits", "limit, powers as exp/log", "SymbolicUtils"),
    ("giac", "Giac", "limit (for reference)", "Giac"),
]

# a small JSON writer, enough for the page's data
json(x::Nothing) = "null"
json(x::Bool) = string(x)
json(x::Real) = isfinite(x) ? string(x) : "null"
function json(s::AbstractString)
    io = IOBuffer(); print(io, '"')
    for c in s
        c == '"' ? print(io, "\\\"") : c == '\\' ? print(io, "\\\\") :
        c == '<' ? print(io, "\\u003c") : c < ' ' ? print(io, "\\u", string(UInt16(c), base = 16, pad = 4)) : print(io, c)
    end
    print(io, '"'); String(take!(io))
end
json(v::AbstractVector) = "[" * join(json.(v), ",") * "]"
json(d::AbstractDict) = "{" * join((json(string(k)) * ":" * json(v) for (k, v) in d), ",") * "}"

# how a limit point and direction are shown: x → 0⁺, x → π/4, x → ∞
showpt(x0) = x0 isa Real && isinf(x0) ? (x0 > 0 ? "∞" : "−∞") : string(x0)
side(x0, dir) = x0 isa Real && isinf(x0) ? "" : dir === :+ ? "⁺" : dir === :- ? "⁻" : ""
showans(a) = a isa Real && isinf(a) ? (a > 0 ? "∞" : "−∞") : replace(string(a), "//" => "/")

problems = [Dict("i" => i, "f" => string(ex), "pt" => showpt(x0) * side(x0, dir), "ans" => showans(ans), "src" => src)
            for (i, (ex, x0, dir, ans, src)) in enumerate(include(joinpath(HERE, "problems.jl")))]
N = length(problems)

versions = Dict{String,String}("Julia" => string(VERSION))
methods = map(METHODS) do (key, pkg, method, terms)
    cells = Vector{Any}(nothing, N)
    loads, wall, limit = Float64[], nothing, nothing
    for line in eachline(joinpath(RESULTS, "results_$key.tsv"))
        p = split(line, '\t')
        if p[1] == "R"
            cells[parse(Int, p[2])] = Dict("s" => p[3], "v" => p[4], "t" => round(parse(Float64, p[5]), digits = 3),
                                           "o" => length(p) > 5 ? p[6] : "")
        elseif p[1] == "L"
            push!(loads, parse(Float64, p[2]))
        elseif p[1] == "T"
            wall = parse(Float64, p[2])
            limit = parse(Float64, p[3])
        elseif p[1] == "V"
            versions[p[2]] = p[3]
        end
    end
    missing = findall(isnothing, cells)
    isempty(missing) || error("$key: no result for problems $missing")
    Dict("key" => key, "pkg" => pkg, "method" => method, "terms" => terms, "cells" => cells,
         "load" => isempty(loads) ? nothing : round(first(loads), digits = 2),
         "restarts" => max(length(loads) - 1, 0),
         "solving" => round(sum(c["t"] for c in cells), digits = 1),
         "wall" => wall === nothing ? nothing : round(wall, digits = 1), "limit" => limit)
end

commits = Dict{String,String}()
f = joinpath(RESULTS, "commits.tsv")
isfile(f) && for line in eachline(f)
    k, v = split(line, '\t'); commits[k] = v
end
date = Libc.strftime("%Y-%m-%d", isfile(f) ? mtime(f) : time())

data = Dict("problems" => problems, "methods" => methods, "date" => date,
            "limit" => maximum(something(m["limit"], 0) for m in methods),
            "versions" => versions, "commits" => commits)
html = replace(read(joinpath(HERE, "template.html"), String), "/*DATA*/null" => json(data))
write(joinpath(RESULTS, "limits_comparison.html"), html)

for m in methods
    k = map(m["cells"]) do c
        c["s"] == "solved" ? c["v"] : c["s"]
    end
    counts = sort([(s, count(==(s), k)) for s in unique(k)], by = last, rev = true)
    println(rpad(m["key"], 22), " ", join(("$s $n" for (s, n) in counts), ", "),
            " | solving $(m["solving"]) s, load $(m["load"]) s, wall $(m["wall"]) s")
end
