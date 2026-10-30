# ---------------------------------------------------------------------------
# Constructors of exp, log, trig and abs atoms; substitution
# ---------------------------------------------------------------------------
# --- exp / log / trig constructors -------------------------------------------
# exp of a sum. Constants are pulled out (exp(c) = exp(1)^c) and so are terms
# c*log(y) (= y^c). The remaining non-constant terms are kept together in ONE
# atom exp(u0)^c, with u0 normalised to have coefficient 1 on its first monomial.
# Splitting them into separate exp atoms would destroy cancellations between the
# terms, e.g. exp(t^2 log(sin(1/t)) + t^2 log t) has a bounded argument although
# each term alone diverges.
function mkexp(u::Sum)
    res = oneS()
    rest = Dict{Mono,Q}()
    for (m, c) in u.t
        a1 = length(m.fs) == 1 ? m.fs[1] : nothing
        if isempty(m.fs)
            a = funatom(:exp, Sum[oneS()])
            res = mulS(res, monoS(Mono(Pair{Atom,Q}[a => c]), Q(1)))
        elseif a1 !== nothing && a1.second == 1 && a1.first.kind === :fun && a1.first.head === :log
            res = mulS(res, powS(a1.first.args[1]::Sum, c))     # exp(c*log y) = y^c
        else
            rest[m] = c
        end
    end
    if !isempty(rest)
        c = first(sort!(collect(rest); by = p -> p.first.key)).second
        u0 = Sum(Dict{Mono,Q}(m => v / c for (m, v) in rest))
        a = funatom(:exp, Sum[u0])
        res = mulS(res, monoS(Mono(Pair{Atom,Q}[a => c]), Q(1)))
    end
    res
end

function factorint(n::BigInt)
    f = Pair{BigInt,Int}[]
    p = big(2)
    while p * p <= n && p < 1_000_000
        k = 0
        while n % p == 0
            n ÷= p
            k += 1
        end
        k > 0 && push!(f, p => k)
        p += (p == 2 ? 1 : 2)
    end
    n > 1 && push!(f, n => 1)
    f
end

function lograt(c::Q)
    res = zeroS()
    for (p, k) in factorint(numerator(c))
        res = addS(res, scaleS(atomS(funatom(:log, Sum[constS(p)])), Q(k)))
    end
    for (p, k) in factorint(denominator(c))
        res = subS(res, scaleS(atomS(funatom(:log, Sum[constS(p)])), Q(k)))
    end
    res
end

function logatom(a::Atom)
    if a.kind === :fun && a.head === :exp
        a.args[1]::Sum
    elseif a.kind === :base
        mklog(a.args[1]::Sum)
    else
        atomS(funatom(:log, Sum[atomS(a)]))
    end
end

function mklog(s::Sum)
    isempty(s.t) && throw(GruntzError("log(0)", :undefined))
    length(s.t) == 1 && _defer_domain(first(s.t).first) && return atomS(funatom(:log, Sum[s]))
    require_positive(s)
    if length(s.t) == 1
        m, c = first(s.t)
        negs, grp = Pair{Atom,Q}[], nothing
        if needs_signs(m, c)
            pf = positive_factors(m, c)
            pf === nothing && throw(GruntzError("log of a negative number", :undefined))
            c, m, negs, grp = pf
        end
        res = lograt(c)
        for (a, e) in m.fs
            res = addS(res, scaleS(logatom(a), e))
        end
        for (a, e) in negs                       # log(a^e) = e log(-a), for a < 0
            res = addS(res, scaleS(atomS(funatom(:log, Sum[negatom(a)])), e))
        end
        grp === nothing || (res = addS(res, atomS(funatom(:log, Sum[grp]))))
        return res
    end
    atomS(funatom(:log, Sum[s]))
end

const PI_ATOM = leafatom(π)

# q for a constant q*π, q rational; otherwise nothing
function piratio(s::Sum)
    length(s.t) == 1 || return nothing
    m, c = first(s.t)
    (length(m.fs) == 1 && m.fs[1].first == PI_ATOM && isone(m.fs[1].second)) ? c : nothing
end

# sin(q*π) exactly, for q with denominator 1, 2, 3, 4 or 6; otherwise nothing
function sinpi_exact(q::Q)
    r = mod(q, 2)
    sg = r >= 1 ? -1 : 1               # sin(π + t) = -sin(t)
    r >= 1 && (r -= 1)
    r > 1//2 && (r = 1 - r)            # sin(π - t) = sin(t)
    half = Q(1) // 2
    v = iszero(r) ? zeroS() : r == half ? oneS() : r == Q(1) // 6 ? constS(half) :
        r == Q(1) // 4 ? scaleS(powS(constS(2), half), half) :
        r == Q(1) // 3 ? scaleS(powS(constS(3), half), half) : nothing
    v === nothing ? nothing : scaleS(v, Q(sg))
end

# sin and cos of a rational multiple of π with a small denominator are evaluated,
# so that zeros such as cos(π/2) are recognised
function mksin(s::Sum)
    isempty(s.t) && return zeroS()
    q = piratio(s)
    v = q === nothing ? nothing : sinpi_exact(q)
    v === nothing ? trigatom(:sin, s) : v
end
function mkcos(s::Sum)
    isempty(s.t) && return oneS()
    q = piratio(s)
    v = q === nothing ? nothing : sinpi_exact(q + Q(1) // 2)   # cos(t) = sin(t + π/2)
    v === nothing ? trigatom(:cos, s) : v
end

# A sin or cos atom, its argument normalised to u + r*π with 0 <= r < 1/2 and the first
# monomial of u with a positive coefficient: the parity and the shifts by multiples of
# π/2 are taken out. Otherwise cos(2t + π) - cos(2t - π), which is 0, is not recognised
# as zero (and its series cancel to every order).
const PI_MONO = Mono(Pair{Atom,Q}[PI_ATOM => Q(1)])
function trigatom(h::Symbol, s::Sum)
    q = get(s.t, PI_MONO, zero(Q))
    u = Sum(Dict{Mono,Q}(m => c for (m, c) in s.t if m != PI_MONO))
    sg = 1
    if !isempty(u.t) && first(sort!(collect(u.t); by = p -> p.first.key)).second < 0
        u, q = negS(u), -q                       # sin(-t) = -sin(t), cos(-t) = cos(t)
        h === :sin && (sg = -sg)
    end
    r = mod(q, 2)
    k = floor(Int, 2r)
    r -= Q(k) // 2
    for _ in 1:k                                 # sin(t + π/2) = cos(t), cos(t + π/2) = -sin(t)
        h === :cos && (sg = -sg)
        h = h === :sin ? :cos : :sin
    end
    arg = iszero(r) ? u : addS(u, scaleS(atomS(PI_ATOM), r))
    scaleS(atomS(funatom(h, Sum[arg])), Q(sg))
end

# atan is odd: pull a negative sign of a single-term argument outside
function mkatan(s::Sum)
    isempty(s.t) && return zeroS()
    if length(s.t) == 1 && first(s.t).second < 0
        return negS(mkatan(negS(s)))
    end
    atomS(funatom(:atan, Sum[s]))
end

# erf is odd, as atan is. erfs(u) = exp(u^2) erfc(u) is the tractable part of erf(u)
# for u -> +oo (see `resolve_piecewise`); it is never built from the input.
function mkerf(s::Sum)
    isempty(s.t) && return zeroS()
    if length(s.t) == 1 && first(s.t).second < 0
        return negS(mkerf(negS(s)))
    end
    atomS(funatom(:erf, Sum[s]))
end
mkerfs(s::Sum) = atomS(funatom(:erfs, Sum[s]))

# gamma. Of a positive integer, evaluated; a pole is an error. An argument with the
# limit variable is shifted by an integer to u + r, 0 <= r < 1, the first monomial of
# u with a positive coefficient: gamma(u + r + n) = (u + r)(u + r + 1)...(u + r + n - 1)
# gamma(u + r), so that ratios such as gamma(x + 2)/gamma(x) cancel to polynomials
# before any asymptotic expansion. lgrem(u) is the remainder of Stirling's series,
# log(gamma(u)) - (u - 1/2) log(u) + u - log(2π)/2, for u -> +oo (see
# `resolve_gamma`); it is never built from the input.
const MAX_GAMMA_SHIFT = 64
function mkgamma(s::Sum)
    r = ratconst(s)
    if r !== nothing && isinteger(r)
        r <= 0 && throw(GruntzError("gamma has a pole at $(r)", :undefined))
        r <= 1000 && return constS(factorial(big(numerator(r)) - 1))
    end
    c = get(s.t, ONEMONO, zero(Q))
    n = floor(BigInt, c)
    u = Sum(Dict{Mono,Q}(m => v for (m, v) in s.t if m != ONEMONO))
    (iszero(n) || isempty(u.t) || abs(n) > MAX_GAMMA_SHIFT || !hasleaf(u, CONTEXT[].x.key)) &&
        return atomS(funatom(:gamma, Sum[s]))
    b = addS(u, constS(c - n))
    g = atomS(funatom(:gamma, Sum[b]))
    if n > 0
        foldl((acc, j) -> mulS(acc, addS(b, constS(j))), 0:Int(n)-1; init = g)
    else
        foldl((acc, j) -> mulS(acc, powS(subS(b, constS(j)), Q(-1))), 1:Int(-n); init = g)
    end
end
mklgrem(s::Sum) = atomS(funatom(:lgrem, Sum[s]))

# abs: |c*m| = |c| * abs(m); sign-normalised so abs(u) and abs(-u) coincide.
# It is eliminated before the limit is computed (see `resolve_piecewise`).
function mkabs(s::Sum)
    isempty(s.t) && return zeroS()
    r = ratconst(s)
    r !== nothing && return constS(abs(r))
    if length(s.t) == 1
        m, c = first(s.t)
        return scaleS(atomS(funatom(:abs, Sum[monoS(m, Q(1))])), abs(c))
    end
    c1 = first(sort!(collect(s.t); by = p -> p.first.key)).second
    atomS(funatom(:abs, Sum[c1 < 0 ? negS(s) : s]))
end

# floor: of a rational constant, evaluated. Otherwise an atom, eliminated before the
# limit is computed (see `resolve_floor`) unless it is a constant with a parameter.
# ceil(u) = -floor(-u).
function mkfloor(s::Sum)
    r = ratconst(s)
    r !== nothing && return constS(floor(r))
    atomS(funatom(:floor, Sum[s]))
end
mkceil(s::Sum) = negS(mkfloor(negS(s)))

# sign: sign(c*m) = sign(c) * sign(m), and sign-normalised as abs is, so sign(-u) =
# -sign(u). Eliminated with abs before the limit is computed.
function mksign(s::Sum)
    isempty(s.t) && return zeroS()
    r = ratconst(s)
    r !== nothing && return constS(sign(r))
    if length(s.t) == 1
        m, c = first(s.t)
        return scaleS(atomS(funatom(:sign, Sum[monoS(m, Q(1))])), Q(sign(c)))
    end
    c1 = first(sort!(collect(s.t); by = p -> p.first.key)).second
    c1 < 0 ? negS(atomS(funatom(:sign, Sum[negS(s)]))) : atomS(funatom(:sign, Sum[s]))
end

function mkfun(h::Symbol, a::Vector{Sum})
    h === :exp ? mkexp(a[1]) :
    h === :log ? mklog(a[1]) :
    h === :sin ? mksin(a[1]) :
    h === :atan ? mkatan(a[1]) :
    h === :erf ? mkerf(a[1]) :
    h === :erfs ? mkerfs(a[1]) :
    h === :gamma ? mkgamma(a[1]) :
    h === :lgrem ? mklgrem(a[1]) :
    h === :abs ? mkabs(a[1]) :
    h === :floor ? mkfloor(a[1]) :
    h === :sign ? mksign(a[1]) :
    h === :cos ? mkcos(a[1]) : throw(GruntzError("unsupported function $h"))
end

function mkpow(a::Sum, b::Sum)
    r = ratconst(b)
    r !== nothing ? powS(a, r) : mkexp(mulS(b, mklog(a)))
end

# --- substitution --------------------------------------------------------------
function subs_atoms(s::Sum, f)::Sum
    res = zeroS()
    for (m, c) in s.t
        term = constS(c)
        for (a, e) in m.fs
            r = f(a)
            r === nothing && (r = rebuild(a, f))
            term = mulS(term, powS(r, e))
        end
        res = addS(res, term)
    end
    res
end
function rebuild(a::Atom, f)
    a.kind === :leaf && return atomS(a)
    a.kind === :base && return subs_atoms(a.args[1]::Sum, f)
    mkfun(a.head, Sum[subs_atoms(u::Sum, f) for u in a.args])
end
