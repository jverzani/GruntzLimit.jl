# ---------------------------------------------------------------------------
# TermInterface <-> canonical form
# ---------------------------------------------------------------------------
function from_number(t)
    t isa Integer && return constS(Q(t))
    t isa Rational && return constS(Q(t))
    if t isa AbstractIrrational
        return t === ℯ ? mkexp(oneS()) : atomS(leafatom(t))
    end
    if t isa AbstractFloat
        isfinite(t) || throw(GruntzError("non-finite number in expression"))
        return constS(rationalize(BigInt, t))
    end
    t isa Complex && throw(GruntzError("complex numbers are not supported"))
    leafS(t)                    # symbolic wrapper types (e.g. Num) that are leaves
end

safe_iscall(t) = try iscall(t) === true catch; false end

const NAMED_CONSTANTS = Dict{String,Any}(
    "pi" => π, "π" => π, "E" => ℯ, "ℯ" => ℯ, "exp(1)" => ℯ,   # SymEngine prints E as exp(1)
    "EulerGamma" => Base.MathConstants.eulergamma,
    "Catalan" => Base.MathConstants.catalan,
    "GoldenRatio" => Base.MathConstants.golden)

# A leaf that is a callable constant (e.g. a symbolic number) is evaluated; a
# variable or parameter cannot be called with no arguments and stays an atom.
function leaf_value(t)
    t isa Function || return nothing
    try
        v = t()
        v isa Real ? v : nothing
    catch
        nothing
    end
end

# Numeric leaves of symbolic packages that are not Julia numbers (e.g. SymEngine's
# `Basic` integers, rationals, floats and named constants such as `E`, `pi`, or
# SymbolicUtils' constants, which print like `2` or `(10//3)`) are recognised
# through their printed form, which is exact and package independent. Only the
# unambiguous names `π` and `ℯ` are taken as constants for leaves that are not
# `Number`s, where a name like `E` could be a variable. Returns a `Sum`, or
# `nothing` for a symbol.
function leaf_number(t)
    if t isa Function
        v = leaf_value(t)
        return v === nothing ? nothing : from_number(v)
    end
    t isa Symbol && return nothing      # an `Expr` variable
    s = string(t)
    m = match(r"^\((.*)\)$", s)
    m === nothing || (s = m.captures[1])
    m = match(r"^(-?\d+)(?:/{1,2}(\d+))?$", s)
    if m !== nothing
        n = parse(BigInt, m.captures[1])
        d = m.captures[2] === nothing ? big(1) : parse(BigInt, m.captures[2])
        return constS(Q(n // d))
    end
    if occursin(r"^-?(\d+\.\d*|\.\d+|\d+)([eE][+-]?\d+)?$", s)
        return constS(rationalize(BigInt, parse(Float64, s)))
    end
    (t isa Number || s in ("π", "ℯ")) || return nothing
    haskey(NAMED_CONSTANTS, s) ? from_number(NAMED_CONSTANTS[s]) : nothing
end

# Constants written as bare symbols in a Julia `Expr`, e.g. :(pi * x)
const EXPR_CONSTANTS = Dict{Symbol,Any}(:pi => π, :π => π, :ℯ => ℯ)

function from_term(t)::Sum
    if safe_iscall(t)
        args = arguments(t)
        isempty(args) || return apply_op(op_or_name(t), Sum[from_term(a) for a in args])
    end
    t isa Union{Integer,Rational,AbstractFloat,AbstractIrrational,Complex} && return from_number(t)
    t isa Symbol && haskey(EXPR_CONSTANTS, t) && return from_number(EXPR_CONSTANTS[t])
    v = leaf_number(t)
    v === nothing ? leafS(t) : v
end

# The operation of a term; when the package gives none (`missing`, as SymEngine does for
# its `ceiling`), the function name it prints, e.g. :ceiling for `ceiling(y)`
function op_or_name(t)
    op = operation(t)
    ismissing(op) || return op
    m = match(r"^([A-Za-z_][A-Za-z_0-9]*)\(", string(t))
    m === nothing ? op : Symbol(m.captures[1])
end

# a leaf: a variable, or a parameter, replaced by its value when one is given
function leafS(t)
    a = leafatom(t)
    v = get(CONTEXT[].subst, a.key, nothing)
    v === nothing ? atomS(a) : v
end

# Functions rewritten in terms of others: f(u) = 1/RECIPROCALS[f](u) and
# f(u) = INVERSES[f](1/u) (Julia's definitions of asec, acsc, acot, ...).
const RECIPROCALS = Dict(:sec => :cos, :csc => :sin, :cot => :tan,
                         :sech => :cosh, :csch => :sinh, :coth => :tanh)
const INVERSES = Dict(:asec => :acos, :acsc => :asin, :acot => :atan,
                      :asech => :acosh, :acsch => :asinh, :acoth => :atanh)

function apply_op(op, a::Vector{Sum})
    n = op isa Symbol ? op : (op isa Function ? nameof(op) : Symbol(string(op)))
    na = length(a)
    half = Q(1) // 2
    if n === :identity && na == 1       # SymbolicUtils wraps constants such as π
        a[1]
    elseif n === :+
        foldl(addS, a; init = zeroS())
    elseif n === :-
        na == 1 ? negS(a[1]) : subS(a[1], foldl(addS, a[2:end]; init = zeroS()))
    elseif n === :*
        foldl(mulS, a; init = oneS())
    elseif n in (:/, ://) && na == 2                  # `//` from rational literals in an `Expr`
        mulS(a[1], powS(a[2], Q(-1)))
    elseif n === :inv && na == 1
        powS(a[1], Q(-1))
    elseif n === :^ && na == 2
        mkpow(a[1], a[2])
    elseif n === :sqrt && na == 1
        powS(a[1], half)
    elseif n === :cbrt && na == 1
        powS(a[1], Q(1) // 3)
    elseif n === :exp && na == 1
        mkexp(a[1])
    elseif n === :log && na == 1
        mklog(a[1])
    elseif n === :log && na == 2
        mulS(mklog(a[2]), powS(mklog(a[1]), Q(-1)))
    elseif n === :atan && na == 1
        mkatan(a[1])
    elseif n === :abs && na == 1
        mkabs(a[1])
    elseif n === :floor && na == 1
        mkfloor(a[1])
    elseif n in (:ceil, :ceiling) && na == 1           # SymEngine prints ceil as ceiling
        mkceil(a[1])
    elseif n === :sin && na == 1
        mksin(a[1])
    elseif n === :cos && na == 1
        mkcos(a[1])
    elseif n === :tan && na == 1
        mulS(mksin(a[1]), powS(mkcos(a[1]), Q(-1)))
    elseif n in (:sinh, :cosh, :tanh) && na == 1
        p, m = mkexp(a[1]), mkexp(negS(a[1]))
        s = scaleS(subS(p, m), half)
        c = scaleS(addS(p, m), half)
        n === :sinh ? s : n === :cosh ? c : mulS(s, powS(c, Q(-1)))
    elseif haskey(RECIPROCALS, n) && na == 1
        powS(apply_op(RECIPROCALS[n], a), Q(-1))      # sec = 1/cos, coth = 1/tanh, ...
    elseif n === :asin && na == 1                     # asin(u) = atan(u / sqrt(1 - u^2))
        mkatan(mulS(a[1], powS(subS(oneS(), mulS(a[1], a[1])), -half)))
    elseif n === :acos && na == 1                     # acos(u) = π/2 - asin(u)
        subS(scaleS(atomS(PI_ATOM), half), apply_op(:asin, a))
    elseif n in (:asec, :acsc, :acot) && na == 1      # asec(u) = acos(1/u), ...
        apply_op(INVERSES[n], Sum[powS(a[1], Q(-1))])
    elseif n === :asinh && na == 1                    # log(u + sqrt(u^2 + 1))
        mklog(addS(a[1], powS(addS(mulS(a[1], a[1]), oneS()), half)))
    elseif n === :acosh && na == 1                    # log(u + sqrt(u^2 - 1))
        mklog(addS(a[1], powS(subS(mulS(a[1], a[1]), oneS()), half)))
    elseif n === :atanh && na == 1                    # log((1 + u)/(1 - u)) / 2
        scaleS(subS(mklog(addS(oneS(), a[1])), mklog(subS(oneS(), a[1]))), half)
    elseif n in (:asech, :acsch, :acoth) && na == 1   # asech(u) = acosh(1/u), ...
        apply_op(INVERSES[n], Sum[powS(a[1], Q(-1))])
    else
        throw(GruntzError("unsupported function/operator `$n` with $na argument(s)"))
    end
end
