# ---------------------------------------------------------------------------
# Splitting into cases
# ---------------------------------------------------------------------------
# The limit is computed under a context; when a sign is needed that the context does
# not decide (`NeedSign`), it is computed again for each sign the context allows,
# the case c = 0 by substituting for a parameter. The result is a tree of cases;
# branches with the same limit are merged.
abstract type CaseTree end
struct Leaf <: CaseTree
    v::Any                       # a Sum, an Infinity or a GruntzError
end
struct Split <: CaseTree
    c::Sum                       # the constant split on
    rels::Vector{Symbol}         # of each branch: :<, :(==), :>, :!=; merged :<=, :>=
    zsub::Any                    # the == branch's substitution key => value, or nothing
    kids::Vector{CaseTree}
end

const MAX_CASES = 64
const MAX_DEPTH = 12

# The constant to split on for a needed sign: a product of parameters is split on
# one factor at a time, log(s) on s - 1.
function split_target(c::Sum)
    c = clear_factors(c)[1]
    vars = Dict{String,Mono}()
    a, k0 = linform(c, vars)
    (length(a) == 1 && abs(k0) <= FM_TOL) || return c
    for (at, _) in only(values(vars)).fs
        atom_sign(at) === nothing || continue
        return at.kind === :leaf ? atomS(at) :
               at.kind === :base ? at.args[1]::Sum :
               at.kind === :fun && at.head === :log ? subS(at.args[1]::Sum, oneS()) :
               at.kind === :fun && at.head in (:abs, :atan) ? at.args[1]::Sum : c
    end
    c
end

function solve_cases(run, ctx::Vector{Cond}, sub::Dict{String,Sum}, x::Atom, depth::Int, count::Ref{Int})
    need = try
        return Leaf(with_context(run, ctx, sub, true, x))
    catch err
        err isa GruntzError && return Leaf(err)
        err isa NeedSign || rethrow()
        err
    end
    (depth >= MAX_DEPTH || count[] >= MAX_CASES) &&
        return Leaf(GruntzError("too many cases"))
    c, rels, zsub = with_context(ctx, sub, true, x) do
        c = split_target(need.c)
        ps = possible_signs(c)
        rels = need.zerotest && c === need.c ?
               [r for (r, ok) in ((:(==), 0 in ps), (:!=, any(!=(0), ps))) if ok] :
               [p < 0 ? :< : p == 0 ? :(==) : :> for p in ps]
        c, rels, (:(==) in rels ? solve_zero(c) : nothing)
    end
    length(rels) < 2 && return Leaf(GruntzError("could not split on the sign of $(skey(c))"))
    rs, kids = Symbol[], CaseTree[]
    for rel in rels
        count[] += 1
        if rel === :(==)
            if zsub === nothing
                push!(rs, rel)
                push!(kids, Leaf(GruntzError("the condition could not be solved for a parameter")))
                continue
            end
            sub2 = with_context(() -> add_subst!(copy(sub), zsub), ctx, sub, false, x)
            ctx2 = with_context(() -> subst_ctx(ctx, sub2), ctx, sub, false, x)
        else
            sub2, ctx2 = sub, [ctx; normcond(c, rel)]
        end
        ctx2 === nothing && continue
        push!(rs, rel)
        push!(kids, solve_cases(run, ctx2, sub2, x, depth + 1, count))
    end
    simplify(Split(c, rs, zsub, kids))
end

function same_value(a, b)
    a isa Sum && b isa Sum && return skey(a) == skey(b)
    a isa Infinity && b isa Infinity && return a.sign == b.sign
    a isa GruntzError && b isa GruntzError && return a.kind == b.kind && (a.kind !== :fail || a.msg == b.msg)
    false
end

# Merges branches with the same limit: c < 0 and c > 0 into c != 0; the case c = 0
# into a neighbour whose limit is the same, or becomes the same with the
# substitution of the case (exp(a) at a = 0 is 1). A split left with one branch is
# that branch.
function simplify(t::Split)
    rels, kids = copy(t.rels), copy(t.kids)
    i = findfirst(==(:!=), rels)
    if i !== nothing && kids[i] isa Split && skey(kids[i].c) == skey(t.c) && all(in((:<, :>)), kids[i].rels)
        k = kids[i]
        deleteat!(rels, i); deleteat!(kids, i)
        append!(rels, k.rels); append!(kids, k.kids)
    end
    at(r) = findfirst(==(r), rels)
    leafv(j) = j !== nothing && kids[j] isa Leaf ? kids[j].v : nothing
    lt, gt = at(:<), at(:>)
    if leafv(lt) !== nothing && leafv(gt) !== nothing && same_value(leafv(lt), leafv(gt))
        rels[lt] = :!=
        deleteat!(rels, gt); deleteat!(kids, gt)
    end
    eq = at(:(==))
    z = leafv(eq)
    if z !== nothing
        function subd(v)
            (v isa Sum && t.zsub !== nothing) || return v
            try
                with_context(() -> substS(v, Dict(t.zsub)), Cond[], Dict{String,Sum}(), false, CONTEXT[].x)
            catch err
                err isa GruntzError || rethrow()
                nothing
            end
        end
        for literal in (true, false), r in (:!=, :<, :>)
            j = at(r)
            v = leafv(j)
            v === nothing && continue
            literal || (v = subd(v))
            (v === nothing || !same_value(z, v)) && continue
            rels[j] = r === :< ? :<= : r === :> ? :>= : r
            deleteat!(rels, eq); deleteat!(kids, eq)
            break
        end
    end
    length(kids) == 1 && return kids[1]
    Split(t.c, rels, t.zsub, kids)
end

function flatten_cases(t::CaseTree, conds::Vector{Tuple{Sum,Symbol}}, out)
    if t isa Leaf
        push!(out, copy(conds) => t.v)
    else
        for (rel, k) in zip(t.rels, t.kids)
            push!(conds, (t.c, rel))
            flatten_cases(k, conds, out)
            pop!(conds)
        end
    end
    out
end

const CondList = Vector{Tuple{Sum,Symbol}}

# whether the conditions `a` imply the condition `l`
implies(a::CondList, l::Tuple{Sum,Symbol}) = !any(r -> satisfiable(push!(copy(a), (l[1], r))), negations(l[2]))

# whether `k` implies `a` or `b`
function covers(k::CondList, a::CondList, b::CondList)
    nots(x) = [(c, r) for (c, rel) in x for r in negations(rel)]
    (isempty(a) || isempty(b)) && return true
    !any(na -> any(nb -> satisfiable([k; na; nb]), nots(b)), nots(a))
end

# Cases of the flattened tree with the same limit are merged when their union is
# described by some of their conditions (a <= 0 and 0 < a < 2 give a < 2), and
# conditions implied by the others of a case are dropped.
function merge_cases(cases)
    prune(a::CondList) = (a = copy(a); i = 1;
        while i <= length(a)
            implies(deleteat!(copy(a), i), a[i]) ? deleteat!(a, i) : (i += 1)
        end; a)
    cases = Any[prune(cs) => v for (cs, v) in cases]
    merged = true
    while merged
        merged = false
        for i in eachindex(cases), j in i+1:length(cases)
            (a, va), (b, vb) = cases[i], cases[j]
            v = matching_value(a, va, b, vb)
            v === nothing && continue
            cands = unique(l -> (skey(l[1]), l[2]),
                           [(c, r) for (c, rel) in [a; b] for r in (rel, rel === :< ? :<= : rel === :> ? :>= : rel)])
            filter!(l -> implies(a, l) && implies(b, l), cands)
            k = nothing
            for n in 0:min(3, length(cands)), sub in subsets_of(cands, n)
                if covers(sub, a, b)
                    k = sub
                    break
                end
            end
            k === nothing && continue
            cases[i] = prune(k) => v
            deleteat!(cases, j)
            merged = true
            break
        end
    end
    cases
end

# The limit for the union of two cases when it is the same in both, possibly after
# substituting the equalities of one case into the other's limit (1 for a == 1, and
# a otherwise, give a)
function matching_value(a::CondList, va, b::CondList, vb)
    same_value(va, vb) && return va
    v = subst_eqs(a, vb)
    v !== nothing && same_value(va, v) && return vb
    v = subst_eqs(b, va)
    v !== nothing && same_value(vb, v) && return va
    nothing
end
function subst_eqs(conds::CondList, v)
    v isa Sum || return nothing
    sub = Dict{String,Sum}()
    for (c, rel) in conds
        rel === :(==) || continue
        sol = solve_zero(substS(c, sub))
        sol === nothing || add_subst!(sub, sol)
    end
    isempty(sub) && return nothing
    try
        substS(v, sub)
    catch err
        err isa GruntzError || rethrow()
        nothing
    end
end

subsets_of(v, n) = n == 0 ? [eltype(v)[]] :
    [[v[i]; s] for i in eachindex(v) for s in subsets_of(v[i+1:end], n - 1)]
