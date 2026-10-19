# ---------------------------------------------------------------------------
# Linear inequalities: Fourier–Motzkin elimination
# ---------------------------------------------------------------------------
# sum(a[v] * v) + k > 0 (strict) or >= 0
struct Ineq
    a::Dict{String,BigFloat}
    k::BigFloat
    strict::Bool
end
negate(a::Dict{String,BigFloat}) = Dict{String,BigFloat}(v => -t for (v, t) in a)

const FM_TOL = big"1e-40"

# Fourier–Motzkin elimination: whether the inequalities have a real solution, the
# monomials taken as independent variables. A system that grows too large is taken
# to be feasible (nothing is pruned).
function feasible(cs::Vector{Ineq})
    while true
        i = findfirst(c -> any(t -> abs(t) > FM_TOL, values(c.a)), cs)
        i === nothing && break
        v = first(u for (u, t) in cs[i].a if abs(t) > FM_TOL)
        pos, neg, rest = Ineq[], Ineq[], Ineq[]
        for c in cs
            t = get(c.a, v, BigFloat(0))
            abs(t) <= FM_TOL ? push!(rest, c) : t > 0 ? push!(pos, c) : push!(neg, c)
        end
        for p in pos, n in neg
            tp, tn = p.a[v], -n.a[v]
            a = Dict{String,BigFloat}()
            for (u, t) in p.a
                u == v || (a[u] = get(a, u, BigFloat(0)) + t / tp)
            end
            for (u, t) in n.a
                u == v || (a[u] = get(a, u, BigFloat(0)) + t / tn)
            end
            push!(rest, Ineq(a, p.k / tp + n.k / tn, p.strict || n.strict))
        end
        cs = rest
        length(cs) > 500 && return true
    end
    all(c -> c.strict ? c.k > FM_TOL : c.k >= -FM_TOL, cs)
end
