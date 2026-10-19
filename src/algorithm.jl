# ---------------------------------------------------------------------------
# Gruntz's algorithm
# ---------------------------------------------------------------------------
const DEPTH = Ref(0)

function limitinf(e::Sum, x::Atom)::Union{Sum,Infinity}
    hasleaf(e, x.key) || return e
    DEPTH[] > 120 && throw(GruntzError("recursion limit reached: the expression is too " *
                                       "complicated for the algorithm as implemented"))
    DEPTH[] += 1
    try
        c0, e0 = mrv_leadterm(e, x)
        if sign(e0) > 0
            zeroS()
        elseif sign(e0) < 0
            s = try
                sgn(c0, x)
            catch err
                err isa NeedSign || rethrow()
                return Infinity(0, err)
            end
            s == 0 && throw(GruntzError("could not determine the sign of the leading coefficient"))
            Infinity(s)
        else
            skey(c0) == skey(e) &&
                throw(GruntzError("no progress: leading coefficient equals the expression"))
            limitinf(c0, x)
        end
    finally
        DEPTH[] -= 1
    end
end

# sign of e as x -> +oo (nonzero for nonzero e)
function sgn(c::Sum, x::Atom)::Int
    hasleaf(c, x.key) || return csign(c)
    if length(c.t) == 1
        m, co = first(c.t)
        sg = co < 0 ? -1 : 1
        simple = true
        for (a, e) in m.fs
            if hasleaf(a, x.key)
                if !(a == x || (a.kind === :fun && a.head === :exp))
                    simple = false
                    break
                end
            else
                s2 = csign(atomS(a))
                s2 == 0 && throw(GruntzError("zero constant factor"))
                if s2 < 0
                    isone(denominator(e)) || throw(GruntzError("complex power", :undefined))
                    isodd(numerator(e)) && (sg = -sg)
                end
            end
        end
        simple && return sg
    end
    L = limitinf(c, x)
    L isa Infinity && return signof(L)
    v = csign(L)
    v != 0 && return v
    c1, _ = mrv_leadterm(c, x)
    sgn(c1, x)
end

logof(a::Atom) = (a.kind === :fun && a.head === :exp) ? a.args[1]::Sum : mklog(atomS(a))

function compare(a::Atom, b::Atom, x::Atom)
    c = limitinf(mulS(logof(a), powS(logof(b), Q(-1))), x)
    c isa Infinity ? :gt : (numzero(c, x) ? :lt : :eq)
end

function mrv_max(f::Vector{Atom}, g::Vector{Atom}, x::Atom)
    isempty(f) && return g
    isempty(g) && return f
    any(a -> a in g, f) && return union(f, g)
    c = compare(f[1], g[1], x)
    c === :gt ? f : c === :lt ? g : union(f, g)
end

function mrv(e::Sum, x::Atom)::Vector{Atom}
    Ω = Atom[]
    hasleaf(e, x.key) || return Ω
    for m in keys(e.t), (a, _) in m.fs
        Ω = mrv_max(Ω, mrv_atom(a, x), x)
    end
    Ω
end

function mrv_atom(a::Atom, x::Atom)::Vector{Atom}
    hasleaf(a, x.key) || return Atom[]
    a.kind === :leaf && return Atom[a]
    a.kind === :base && return mrv(a.args[1]::Sum, x)
    if a.head === :exp
        u = a.args[1]::Sum
        L = limitinf(u, x)
        return L isa Infinity ? mrv_max(Atom[a], mrv(u, x), x) : mrv(u, x)
    end
    Ω = Atom[]
    for u in a.args
        Ω = mrv_max(Ω, mrv(u::Sum, x), x)
    end
    Ω
end

function single_atom(s::Sum)
    length(s.t) == 1 || return nothing
    m, c = first(s.t)
    (isone(c) && length(m.fs) == 1) ? m.fs[1].first : nothing
end

# returns (c0, e0) with e = c0 * w^e0 + ..., w -> 0+ the exponential of the mrv class
function mrv_leadterm(e::Sum, x::Atom)
    Ω = mrv(e, x)
    isempty(Ω) && return e, EX0
    if any(==(x), Ω)
        # move up: x -> exp(x). The mrv set is mapped, never recomputed (avoids infinite recursion).
        xup = mkexp(atomS(x))
        up = a -> a == x ? xup : nothing
        newΩ = Atom[]
        ok = true
        for a in Ω
            at = single_atom(subs_atoms(atomS(a), up))
            (at === nothing || at.kind !== :fun || at.head !== :exp) ? (ok = false) : push!(newΩ, at)
        end
        e = subs_atoms(e, up)
        # members that no longer occur (x of log(x), now x) are dropped, unless none
        # is left: a w made from one would give every term a power of w with a
        # parameter (x^a, a free)
        occurring = filter(a -> hasatom(e, a.key), newΩ)
        isempty(occurring) || (newΩ = occurring)
        Ω = ok ? newΩ : mrv(e, x)
        any(==(x), Ω) && throw(GruntzError("internal error while moving up"))
    end
    sort!(Ω; by = a -> length(a.key))
    g1 = Ω[1].args[1]::Sum
    σ = sgn(g1, x)
    wS = atomS(WLEAF)
    wpow = Dict{String,Sum}()      # exp(g_i) = w^(-σ c_i) * exp(g_i - c_i g_1)
    rest = Dict{String,Sum}()      # g_i - c_i g_1
    for a in Ω
        gi = a.args[1]::Sum
        ci = limitinf(mulS(gi, powS(g1, Q(-1))), x)
        ci isa Infinity && throw(GruntzError("internal error: mrv class is inconsistent"))
        cq = ratconst(ci)
        iszero(ci) && throw(GruntzError("internal error: mrv class is inconsistent"))
        if cq === nothing      # an irrational ratio: w^(-σ ci) is a leaf of its own
            wpow[a.key] = atomS(wpowatom(scaleS(ci, Q(-σ))))
            rest[a.key] = subS(gi, mulS(g1, ci))
        else
            wpow[a.key] = powS(wS, Q(-σ) * cq)
            rest[a.key] = subS(gi, scaleS(g1, cq))
        end
    end
    # The factor exp(g_i - c_i g_1) may itself contain members of Ω inside its
    # argument (e.g. exp(exp(-x)) = exp(w)), so it is rewritten recursively.
    memo = Dict{String,Sum}()
    function rewrite(a::Atom)
        haskey(wpow, a.key) || return nothing
        haskey(memo, a.key) && return memo[a.key]
        v = mulS(wpow[a.key], subs_atoms(mkexp(rest[a.key]), rewrite))
        memo[a.key] = v
        v
    end
    f = subs_atoms(e, rewrite)
    leadterm(f, WLEAF, scaleS(g1, Q(-σ)), x)   # log(w) = -σ g1
end
