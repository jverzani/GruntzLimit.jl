# ---------------------------------------------------------------------------
# Complex values
# ---------------------------------------------------------------------------
# An input with the imaginary unit (or complex numbers) is converted into its real and
# imaginary parts, re + i im, each a real expression in the canonical form. The
# operations are those of complex numbers written with real functions:
#
#     exp(a + ib) = exp(a) (cos b + i sin b)
#     log(a + ib) = log(a^2 + b^2)/2 + i arg(a, b)
#     (a + ib)^q  = (a^2 + b^2)^(q/2) (cos(q arg) + i sin(q arg)),  q rational
#     z^w         = exp(w log z)
#     sin, cos (with cosh and sinh of the imaginary part), and functions written with
#     them or exp (tan, sinh, cosh, tanh, sec, ...)
#     atan(z)     = i/2 (log(1 - i*z) - log(1 + i*z)),  the principal branch
#
# with `arg(a, b)` the principal argument, in (-π, π], an atom resolved like abs once
# the sign of `a` near the limit point is known (see `resolve_carg`). Other functions of
# a complex argument are not supported. The limits of the two parts are taken
# separately (see `limit_value`), so the limit of exp(-(2 + 3i) x) at +oo is that of
# exp(-2x) cos(3x) and of -exp(-2x) sin(3x), both 0. An input whose imaginary part
# turns out to be 0 is an ordinary real one. In a complex input, fractional powers and
# logs of negative constants take their principal values ((-1)^(1/2) = i, as SymJ
# writes i); of expressions in x, they are real as elsewhere.
struct CS
    re::Sum
    im::Sum
end
realC(s::Sum) = CS(s, zeroS())
isrealC(z::CS) = iszero(z.im)

# i in results (see `user_value`)
const IM_ATOM = leafatom(im)

# A number c in a complex leaf, printed as "-2 - 3*im" (SymEngine), "(0 + 1im)"
# (SymbolicUtils) or "im"; nothing otherwise
const _RNUM = raw"\d+(?:\.\d*)?(?:[eE][+-]?\d+)?(?://?\d+)?"
const _CPLX = Regex("^(?:([+-]?" * _RNUM * ")(?=[+-]))?([+-]?)(" * _RNUM * ")?im\$")
function complex_leaf(t)
    t isa Complex && return CS(from_number(real(t)), from_number(imag(t)))
    t isa Symbol && return t === :im ? CS(zeroS(), oneS()) : nothing
    t isa Real && return nothing
    if t isa Function                    # a callable constant (SimpleExpressions)
        v = try t() catch; nothing end
        return v isa Complex ? complex_leaf(v) : nothing
    end
    s = replace(string(t), " " => "", "*" => "")
    m = match(r"^\((.*)\)$", s)
    m === nothing || (s = m.captures[1])
    m = match(_CPLX, s)
    m === nothing && return nothing
    pnum(u) = (u = replace(u, "//" => "/"); occursin('/', u) ?
        (p = split(u, '/'); constS(Q(parse(BigInt, p[1]) // parse(BigInt, p[2])))) :
        occursin(r"[.eE]", u) ? constS(rationalize(BigInt, parse(Float64, u))) : constS(Q(parse(BigInt, u))))
    re = m.captures[1] === nothing ? zeroS() : pnum(m.captures[1])
    im_ = m.captures[3] === nothing ? oneS() : pnum(m.captures[3])
    CS(re, m.captures[2] == "-" ? negS(im_) : im_)
end

# whether the term has the imaginary unit or a complex number in it; also a square root
# of a negative number, as SymJ writes i: (-1)^(1/2)
function has_complex(t)
    if safe_iscall(t)
        args = arguments(t)
        if !isempty(args)
            length(args) == 2 && op_or_name(t) in (^, :^) && negsqrt(args...) && return true
            length(args) == 1 && opname(op_or_name(t)) === :cosint && return true   # see apply_op_c
            length(args) == 2 && opname(op_or_name(t)) in (:besselk, :besseli) && return true
            return any(has_complex, args)
        end
    end
    t isa Complex && return !iszero(imag(t))
    complex_leaf(t) !== nothing
end

function negsqrt(b, e)
    small(t) = !safe_iscall(t) || all(a -> !safe_iscall(a), arguments(t))   # -1, 1//2
    (small(b) && small(e)) || return false
    vb, ve = try
        from_term(b), from_term(e)
    catch err
        err isa GruntzError || rethrow()
        return false
    end
    rb, re = ratconst(vb), ratconst(ve)
    rb !== nothing && re !== nothing && rb < 0 && denominator(re) == 2
end

function from_term_c(t)::CS
    if safe_iscall(t)
        args = arguments(t)
        isempty(args) || return apply_op_c(op_or_name(t), CS[from_term_c(a) for a in args])
    end
    z = complex_leaf(t)
    z === nothing ? realC(from_term(t)) : z
end

cadd(a::CS, b::CS) = CS(addS(a.re, b.re), addS(a.im, b.im))
cneg(a::CS) = CS(negS(a.re), negS(a.im))
cmul(a::CS, b::CS) = CS(subS(mulS(a.re, b.re), mulS(a.im, b.im)), addS(mulS(a.re, b.im), mulS(a.im, b.re)))
cscale(a::CS, s::Sum) = CS(mulS(a.re, s), mulS(a.im, s))
abs2C(a::CS) = cancel_base(addS(mulS(a.re, a.re), mulS(a.im, a.im)))

# s = N B^(-e), B a multi-term base dividing every term, with N a constant times B^e
# expanded: that constant. |(x - i)/(-x - i)|² is ((1 - x²)² + 4x²)/(1 + x²)², which is 1;
# otherwise its log is a zero the series cannot find.
function cancel_base(s::Sum)
    length(s.t) < 2 && return s
    ms = collect(keys(s.t))
    for (a, _) in ms[1].fs
        a.kind === :base || continue
        es = [sum((e for (b, e) in m.fs if b == a); init = Q(0)) for m in ms]
        e = -maximum(es)
        (e > 0 && isinteger(e) && e <= 8 && all(==(es[1]), es)) || continue
        N = mulS(s, powS(atomS(a), e))
        P = powS(a.args[1]::Sum, e)
        (isempty(N.t) || isempty(P.t)) && continue
        mP, cP = first(P.t)
        c = get(N.t, mP, nothing)
        c === nothing && continue
        skey(N) == skey(scaleS(P, c / cP)) && return constS(c / cP)
    end
    s
end
function cinv(a::CS)
    isrealC(a) && return realC(powS(a.re, Q(-1)))
    d = powS(abs2C(a), Q(-1))
    CS(mulS(a.re, d), negS(mulS(a.im, d)))
end
cexp(a::CS) = isrealC(a) ? realC(mkexp(a.re)) : cscale(CS(mkcos(a.im), mksin(a.im)), mkexp(a.re))
function clog(a::CS)
    isrealC(a) && !negconst(a.re) && return realC(mklog(a.re))
    CS(scaleS(mklog(abs2C(a)), Q(1) // 2), mkcarg(a.re, a.im))
end
function cpowq(a::CS, q::Q)
    if isrealC(a)        # a negative constant: its principal root, (-1)^(1/2) = i
        isone(denominator(q)) || !negconst(a.re) || return polarpow(a, q)
        return realC(powS(a.re, q))
    end
    if isone(denominator(q)) && abs(q) <= 64
        n = Int(abs(numerator(q)))
        r, b = CS(oneS(), zeroS()), a
        while n > 0                              # by squaring
            isodd(n) && (r = cmul(r, b))
            n >>= 1
            n > 0 && (b = cmul(b, b))
        end
        return q < 0 ? cinv(r) : r
    end
    polarpow(a, q)
end
function polarpow(a::CS, q::Q)
    θ = scaleS(mkcarg(a.re, a.im), q)
    cscale(CS(mkcos(θ), mksin(θ)), powS(abs2C(a), q / 2))
end
function cpow(a::CS, b::CS)
    if isrealC(b)
        r = ratconst(b.re)
        r === nothing || return cpowq(a, r)
        isrealC(a) && return realC(mkpow(a.re, b.re))
    end
    cexp(cmul(b, clog(a)))
end
csin(a::CS) = CS(mulS(mksin(a.re), apply_op(:cosh, Sum[a.im])), mulS(mkcos(a.re), apply_op(:sinh, Sum[a.im])))
ccos(a::CS) = CS(mulS(mkcos(a.re), apply_op(:cosh, Sum[a.im])), negS(mulS(mksin(a.re), apply_op(:sinh, Sum[a.im]))))

function apply_op_c(op, a::Vector{CS})::CS
    n = op isa Symbol ? op : (op isa Function ? nameof(op) : Symbol(string(op)))
    na = length(a)
    # parts of a complex number, real or not
    n === :real && na == 1 && return realC(a[1].re)
    n === :imag && na == 1 && return realC(a[1].im)
    n === :conj && na == 1 && return CS(a[1].re, negS(a[1].im))
    n in (:angle, :arg) && na == 1 && return realC(mkcarg(a[1].re, a[1].im))
    n in (:abs2,) && na == 1 && return realC(abs2C(a[1]))
    # cosint of a real argument in x, on its principal branch: Ci(u) = Ci(|u|) + iπ for
    # u < 0, so Ci(u) = Ci(|u|) + iπ (1 - sign(u))/2, decided at the limit point
    if n === :cosint && na == 1 && isrealC(a[1]) && hasleaf(a[1].re, CONTEXT[].x.key)
        u = a[1].re
        return CS(mkcosint(mkabs(u)), scaleS(mulS(atomS(PI_ATOM), subS(oneS(), mksign(u))), Q(1) // 2))
    end
    # on retrying a real expression whose log or fractional power met a negative
    # argument (see `limit_value`): on the principal branch, log(u) = log|u| + iπ (1 -
    # sign(u))/2 and u^q = |u|^q exp(iqπ (1 - sign(u))/2), the sign decided at the limit
    if BRANCH_X[] && all(isrealC, a) && hasleaf(a[1].re, CONTEXT[].x.key)
        u = a[1].re
        q = n === :sqrt && na == 1 ? Q(1) // 2 :
            n === :^ && na == 2 ? (r = ratconst(a[2].re); r !== nothing && !isinteger(r) ? r : nothing) : nothing
        neg = scaleS(subS(oneS(), mksign(u)), Q(1) // 2)
        if n === :log && na == 1
            return CS(mklog(mkabs(u)), mulS(atomS(PI_ATOM), neg))
        elseif q !== nothing
            θ = mulS(scaleS(atomS(PI_ATOM), q), neg)
            m = powS(mkabs(u), q)
            return CS(mulS(m, mkcos(θ)), mulS(m, mksin(θ)))
        end
    end
    # besselk and besseli of a real argument in x, on their principal branches: for v > 0,
    # K_ν(-v) = exp(-iνπ) K_ν(v) - iπ I_ν(v) and I_ν(-v) = exp(iνπ) I_ν(v) (DLMF 10.34.1-2)
    if n in (:besselk, :besseli) && na == 2 && all(isrealC, a) && hasleaf(a[2].re, CONTEXT[].x.key)
        ν, u = a[1].re, a[2].re
        r = ratconst(ν)
        r === nothing && throw(GruntzError("$n is supported only for a rational order"))
        n === :besselk && (r = abs(r))
        s, au = mksign(u), mkabs(u)
        pos, neg = scaleS(addS(oneS(), s), Q(1) // 2), scaleS(subS(oneS(), s), Q(1) // 2)
        θ = scaleS(atomS(PI_ATOM), r)
        if n === :besselk
            K = mkbesselk(ν, au)
            return CS(mulS(K, addS(pos, mulS(mkcos(θ), neg))),
                      negS(mulS(neg, addS(mulS(mksin(θ), K), mulS(atomS(PI_ATOM), mkbesseli(constS(r), au))))))
        end
        isinteger(r) && return realC(mkbesseli(ν, u))
        I = mkbesseli(ν, au)
        return CS(mulS(I, addS(pos, mulS(mkcos(θ), neg))), mulS(I, mulS(mksin(θ), neg)))
    end
    # a real expression is an ordinary one, except for the principal value of a power, a
    # square root or a log of a negative constant: (-1)^(1/2) = i
    all(isrealC, a) && !(n in (:^, :sqrt, :log) && negconst(a[1].re) &&
                          (n !== :^ || (r = ratconst(a[2].re); r !== nothing && !isinteger(r)))) &&
        return realC(apply_op(op, Sum[z.re for z in a]))
    half = Q(1) // 2
    if n === :identity && na == 1
        a[1]
    elseif n === :+
        foldl(cadd, a; init = CS(zeroS(), zeroS()))
    elseif n === :-
        na == 1 ? cneg(a[1]) : cadd(a[1], cneg(foldl(cadd, a[2:end]; init = CS(zeroS(), zeroS()))))
    elseif n === :*
        foldl(cmul, a; init = CS(oneS(), zeroS()))
    elseif n in (:/, ://) && na == 2
        cmul(a[1], cinv(a[2]))
    elseif n === :inv && na == 1
        cinv(a[1])
    elseif n === :^ && na == 2
        cpow(a[1], a[2])
    elseif n === :sqrt && na == 1
        cpowq(a[1], half)
    elseif n === :exp && na == 1
        cexp(a[1])
    elseif n === :cis && na == 1                      # cis(u) = exp(iu)
        cexp(CS(negS(a[1].im), a[1].re))
    elseif n === :log && na == 1
        clog(a[1])
    elseif n === :abs && na == 1
        realC(powS(abs2C(a[1]), half))
    elseif n === :sin && na == 1
        csin(a[1])
    elseif n === :cos && na == 1
        ccos(a[1])
    elseif n === :tan && na == 1
        cmul(csin(a[1]), cinv(ccos(a[1])))
    elseif n in (:sinh, :cosh, :tanh) && na == 1
        p, m = cexp(a[1]), cexp(cneg(a[1]))
        s = cscale(cadd(p, cneg(m)), constS(half))
        c = cscale(cadd(p, m), constS(half))
        n === :sinh ? s : n === :cosh ? c : cmul(s, cinv(c))
    elseif n === :atan && na == 1                     # atan(z) = i/2 (log(1 - i*z) - log(1 + i*z))
        z = a[1]
        l1 = clog(CS(addS(oneS(), z.im), negS(z.re)))
        l2 = clog(CS(subS(oneS(), z.im), z.re))
        cmul(CS(zeroS(), constS(half)), cadd(l1, cneg(l2)))
    elseif n in (:erf, :erfc) && na == 1 && hasleaf(a[1].re, CONTEXT[].x.key)
        e = cerf(a[1])
        n === :erf ? e : cadd(CS(oneS(), zeroS()), cneg(e))
    elseif haskey(RECIPROCALS, n) && na == 1
        cinv(apply_op_c(RECIPROCALS[n], a))
    else
        throw(GruntzError("`$n` of a complex argument is not supported"))
    end
end

# The principal argument of a + ib, in (-π, π]. For a and b free of x with a known sign
# it is computed at once; otherwise kept as an atom until the sign of a near the limit
# point is known (see `resolve_carg`).
function mkcarg(a::Sum, b::Sum)
    xk = CONTEXT[].x.key
    (hasleaf(a, xk) || hasleaf(b, xk)) && return atomS(funatom(:carg, Sum[a, b]))
    carg_value(csign(a), a, b, () -> csign(b))
end
function carg_value(sa::Int, a::Sum, b::Sum, sb)
    halfpi = scaleS(atomS(PI_ATOM), Q(1) // 2)
    if sa == 0
        s = sb()
        s == 0 && throw(GruntzError("the argument of 0 is not defined", :undefined))
        return scaleS(halfpi, Q(s))
    end
    t = iszero(b) ? zeroS() : mkatan(mulS(b, powS(a, Q(-1))))
    sa > 0 && return t
    s = iszero(b) ? 1 : sb()
    addS(t, scaleS(atomS(PI_ATOM), Q(s >= 0 ? 1 : -1)))   # a < 0: arg in (π/2, π] or (-π, -π/2)
end
# erf(z), z = u + iv with u in x, as σ (1 - exp(-z²) erfcx(σz)), σ = sign(u). erfcx of an
# argument with a nonnegative real part is the Faddeeva function w(iσz), of modulus at
# most 1, so its parts are bounded atoms, erfcxre and erfcxim (see `rate_atom`). For
# u -> ±oo with v² - u² -> -oo, exp(-z²) decays and erf(z) -> σ, decided by
# `bounded_limit`; at a finite point erfcx of a complex argument is not supported.
function cerf(z::CS)
    σ = mksign(z.re)
    p, q = mulS(σ, z.re), mulS(σ, z.im)
    E = CS(atomS(funatom(:erfcxre, Sum[p, q])), atomS(funatom(:erfcxim, Sum[p, q])))
    cscale(cadd(CS(oneS(), zeroS()), cneg(cmul(cexp(cneg(cmul(z, z))), E))), σ)
end

function resolve_carg(a::Sum, b::Sum, x::Atom)
    sgnof(u) = iszero(u) ? 0 : hasleaf(u, x.key) ? sgn(u, x) : csign(u)
    carg_value(sgnof(a), a, b, () -> sgnof(b))
end
