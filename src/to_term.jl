# ---------------------------------------------------------------------------
# Canonical form -> terms of the input's type
# ---------------------------------------------------------------------------
const OPS = Dict{Symbol,Function}(:+ => +, :* => *, :^ => ^, :exp => exp, :log => log,
                                  :sin => sin, :cos => cos, :atan => atan, :abs => abs,
                                  :sqrt => sqrt, :floor => floor, :sign => sign,
                                  :erf => SpecialFunctions.erf, :erfs => SpecialFunctions.erfcx)
default_build(op, args...) = op(args...)

# Build `op(args...)` for constant arguments WITHOUT evaluating it, for callable
# symbolic types that defer evaluation only when a symbolic variable is involved
# (SimpleExpressions, SymJ). Plain Julia would turn e.g. sqrt(2) or (-1//2)*π into a
# Float64 at once. The term is built with TermInterface's `maketerm`, trying both
# conventions for `head`, a power with exponent p/2 or p/3 from sqrt or cbrt (see
# `root_power`); failing that, the operation is evaluated (the result is then a
# plain number).
# These run a few times per result, for many operations and argument types:
# `@nospecialize` compiles them once instead of once per combination (which cost
# 25-45 ms of compilation per operation on first use).
function maketerm_call(T, op, args)
    @nospecialize
    for TT in unique(Any[T, Base.typename(T).wrapper])
        for attempt in (() -> maketerm(TT, op, Any[args...], nothing),
                        () -> maketerm(TT, :call, Any[op; args...], nothing))
            try
                r = attempt()
                r isa Function && return r
            catch
            end
        end
    end
    nothing
end

function deferred_call(x, op, args)
    @nospecialize
    mt(o, a) = maketerm_call(typeof(x), o, a)
    if op === (^) && length(args) == 2
        r = root_power(mt, args[1], args[2])
        r === nothing || return r
    end
    r = mt(op, args)
    r === nothing ? op(args...) : r
end

# n^e for a number n and e = p/2 or p/3, from sqrt(n) or cbrt(n) built by `mt(op,
# args)`: term types may fold a numeric power to a float, but keep a root exact.
# nothing for another exponent, or when the root is not built.
function root_power(mt, n, e)
    @nospecialize
    (e isa Rational && denominator(e) in (2, 3)) || return nothing
    root = mt(denominator(e) == 2 ? sqrt : cbrt, Any[n])
    root === nothing ? nothing : isone(numerator(e)) ? root : root^numerator(e)
end

expr_build(op, args...) = Expr(:call, nameof(op), args...)

# Term types that are neither numbers nor callable (SymbolicUtils): a call on
# plain numbers only is built with `maketerm` for the type of the variable, which
# keeps it unevaluated (sqrt(2), not 1.414…). A power of a number with exponent
# p/2 or p/3 is built from sqrt or cbrt, as such types may fold numeric powers to
# floats. Anything else applies the operation.
function term_build(x)
    T = typeof(x)
    mt(op, args) = (r = try maketerm(T, op, Any[args...], nothing) catch; nothing end; r isa T ? r : nothing)
    function build(op, args...)
        all(a -> a isa Number, args) || return op(args...)
        if op === (^) && length(args) == 2
            n, e = args
            e isa Integer && n isa Union{Integer,Rational} && return num(Q(n)^e)
            r = root_power(mt, n, e)
            r === nothing || return r
        end
        r = mt(op, args)
        r === nothing ? op(args...) : r
    end
end

# A constant such as π is turned into a term of the variable's type through
# `maketerm(T, identity, [π])` (how SymbolicUtils represents it), else left as is.
function term_lift(x)
    T = typeof(x)
    v -> v isa AbstractIrrational ?
         (r = try maketerm(T, identity, Any[v], nothing) catch; nothing end; r isa T ? r : v) : v
end

# A term type that is neither a Julia number (SymEngine), callable
# (SimpleExpressions) nor a `Symbol` (`Expr`), e.g. SymbolicUtils.
other_terms(x) = !(x isa Number || x isa Function || x isa Symbol)

# Default builder. Julia `Expr`s (variable given as a `Symbol`) are built as
# unevaluated calls, so results stay exact and may contain parameters.
# Function-like symbolic types (SimpleExpressions) defer evaluation only when
# some argument is symbolic; for constant-only terms we construct the node
# explicitly. Numeric types (e.g. SymEngine's `Basic`) simply apply the
# operation, which stays symbolic through their own number type. Other term
# types use `term_build`.
function auto_build(f, x)
    x isa Symbol && return expr_build
    other_terms(x) && return term_build(x)
    typeof(x) <: Function || return default_build
    function (op, args...)
        @nospecialize
        any(a -> a isa Function, args) ? op(args...) : deferred_call(x, op, args)
    end
end

# `build(op, args...)` constructs a compound term; `lift(v)` turns plain Julia
# numbers (and π) into the symbolic package's own number type.
struct Builder
    build::Any
    lift::Any
end
mk(bd::Builder, name::Symbol, args) = bd.build(OPS[name], args...)

fitint(n::BigInt) = typemin(Int) <= n <= typemax(Int) ? Int(n) : n
function num(c::Q)
    n, d = numerator(c), denominator(c)
    isone(d) && return fitint(n)
    (typemin(Int) <= n <= typemax(Int) && d <= typemax(Int)) ? Int(n) // Int(d) : c
end

atom_term(b, a::Atom) =
    a.kind === :leaf ? (a.head isa AbstractIrrational ? b.lift(a.head) : a.head) :
    a.kind === :base ? to_term(b, a.args[1]::Sum) :
    mk(b, a.head, Any[to_term(b, a.args[1]::Sum)])

function mono_term(b, m::Mono, c::Q)
    fs = Any[]
    for (a, e) in m.fs
        t = atom_term(b, a)
        push!(fs, isone(e) ? t : e == Q(1) // 2 ? mk(b, :sqrt, Any[t]) :
                  mk(b, :^, Any[t, b.lift(num(e))]))
    end
    isempty(fs) && return b.lift(num(c))
    isone(c) && return length(fs) == 1 ? fs[1] : mk(b, :*, fs)
    pushfirst!(fs, b.lift(num(c)))      # not Any[c; fs]: a generic vcat to compile
    mk(b, :*, fs)
end

function to_term(b, s::Sum)
    isempty(s.t) && return b.lift(0)
    ts = Any[mono_term(b, m, c) for (m, c) in sort!(collect(s.t); by = p -> p.first.key)]
    length(ts) == 1 ? ts[1] : mk(b, :+, ts)
end

# Callable term types (SimpleExpressions): a constant such as π becomes a term,
# π * one(x), the same as a user writes it.
function callable_lift(x)
    v -> v isa AbstractIrrational ? (try v * one(x) catch; v end) : v
end

# Symbolic number types that are not `Real` (e.g. SymEngine's `Basic`) are built
# from plain numbers by their constructor, so results like exp(1) stay exact.
function auto_lift(f, x)
    for t in (f, x)
        if t isa Number && !(t isa Real)
            T = typeof(t)
            return v -> try
                T(v)
            catch
                v
            end
        end
    end
    other_terms(x) ? term_lift(x) : x isa Function ? callable_lift(x) : identity
end
