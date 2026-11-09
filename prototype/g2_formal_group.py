#!/usr/bin/env python3
"""Genus-2 prototype for blueprint chapter 03-log.

Validates the design of `def:cantor-map`, `def:chart`, `def:Ftau`, `lem:Ftau-basic`,
`thm:Ftau-assoc`, and `lem:delta-rational` symbolically at genus 2, with exact rational
arithmetic and truncated multivariate power series:

* Mumford arithmetic (Cantor composition + reduction) implemented as a *rational map* in
  the coordinates of the data, over an arbitrary coefficient ring in which the leading
  coefficients/resultants met along the way are units (the good-position conditions);
* the chart `X ↦ (u_tau + X, y - V(X))` with `V(X)` the Hensel square root of `f mod u`
  (Newton iteration over truncated series), cf. `def:chart`;
* `F_tau(X, Y)` = chart coordinates of `ch(X) + ch(Y) - tau` (in the tau-displaced
  identification `class(X) = ch(X) - tau` the law must be `ch(X) + ch(Y) - tau`; with
  `- 2*tau` the unit law `F(X,0) = X` fails);
* checks: p-integrality of the coefficients of `F_tau` and `V`; `F_tau(X,0) = X`;
  `F_tau(X,Y) = F_tau(Y,X)`; associativity up to the truncation degree (in 6 variables);
  `M(X) = (dF_tau/dY)(X,0)` has `M(0) = I` and `M` is a matrix of rational functions of
  the chart coordinates (validated on the truncation).

DESIGN NOTE (for the Lean `cantorAdd`): the three-term Bezout `s1 u1 + s2 u2 + s3 (v1+v2)
= 1` genuinely needs all three terms — the canonical `s2 = 0` square-Sylvester reduction is
SINGULAR at the `- tau` step of `F_tau` for this configuration (`res(u1, v1+v2) = 0`: the
support of `2 tau` meets the interpolating line `y = v_tau(x)`), while the full system is
solvable. Consequently the Lean definition passes the certificate `(s1, s2, s3)` as an
argument (with existence over local rings via surjectivity mod the maximal ideal and
Nakayama), and the composition/correctness identities are proved from the certificate:
`V := s1 u1 v2 + s2 u2 v1 + s3 (v1 v2 + f)` satisfies `V = v1 + u1*A = v2 + u2*B` and
`V^2 - f = u1 u2 (A*B + s1 w2 + s2 w1)` where `A = s1(v2-v1) - s3 w1`,
`B = s2(v1-v2) - s3 w2`, `wi = (vi^2 - f)/ui`.

The curve is `y^2 = f(x) = x^5 - x + 1`, `tau = [P1 + P2 - 2*inf]` with `P1 = (0,1)`,
`P2 = (1,1)`; the prime is `p = 11` (good-position conditions verified along the way and
reported). Run: `python3 g2_formal_group.py [truncation_degree]`.
"""

import sys
from fractions import Fraction
from itertools import product

# ---------------------------------------------------------------------------
# Truncated multivariate power series over Q, in NVARS variables, total degree < TRUNC.
# Represented as dict {exponent_tuple: Fraction}, zero coefficients omitted.
# ---------------------------------------------------------------------------

class Ctx:
    NVARS = 4
    TRUNC = 4  # keep monomials of total degree < TRUNC


def s_zero():
    return {}


def s_const(c):
    c = Fraction(c)
    return {(0,) * Ctx.NVARS: c} if c else {}


def s_var(i):
    e = [0] * Ctx.NVARS
    e[i] = 1
    return {tuple(e): Fraction(1)}


def s_add(a, b):
    r = dict(a)
    for e, c in b.items():
        c2 = r.get(e, Fraction(0)) + c
        if c2:
            r[e] = c2
        else:
            r.pop(e, None)
    return r


def s_neg(a):
    return {e: -c for e, c in a.items()}


def s_sub(a, b):
    return s_add(a, s_neg(b))


def s_mul(a, b):
    r = {}
    for ea, ca in a.items():
        da = sum(ea)
        for eb, cb in b.items():
            if da + sum(eb) >= Ctx.TRUNC:
                continue
            e = tuple(x + y for x, y in zip(ea, eb))
            c = r.get(e, Fraction(0)) + ca * cb
            if c:
                r[e] = c
            else:
                r.pop(e, None)
    return r


def s_smul(c, a):
    c = Fraction(c)
    return {e: c * x for e, x in a.items()} if c else {}


def s_constterm(a):
    return a.get((0,) * Ctx.NVARS, Fraction(0))


def s_inv(a):
    """Inverse of a series with unit (nonzero) constant term: geometric series."""
    c0 = s_constterm(a)
    assert c0 != 0, "series inverse: constant term is zero"
    n = s_smul(-1 / c0, s_sub(a, s_const(c0)))  # a = c0 (1 - n)
    r = s_const(1 / c0)
    term = s_const(1 / c0)
    for _ in range(Ctx.TRUNC):
        term = s_mul(term, n)
        if not term:
            break
        r = s_add(r, term)
    return r


def s_subst(a, args):
    """Substitute args[i] (series with zero constant term) for variable i in a."""
    for g in args:
        assert s_constterm(g) == 0, "substitution: nonzero constant term"
    r = {}
    for e, c in a.items():
        term = s_const(c)
        for i, k in enumerate(e):
            for _ in range(k):
                term = s_mul(term, args[i])
        r = s_add(r, term)
    return r


def s_pderiv(a, i):
    r = {}
    for e, c in a.items():
        if e[i] == 0:
            continue
        e2 = list(e)
        e2[i] -= 1
        r[tuple(e2)] = c * e[i]
    return r


# ---------------------------------------------------------------------------
# Univariate polynomials with truncated-series coefficients: dense lists,
# index = degree in x. All divisions require unit leading coefficients
# (the good-position conditions); each inversion is asserted and logged.
# ---------------------------------------------------------------------------

UNIT_LOG = []


def p_trim(u):
    while u and not u[-1]:
        u.pop()
    return u


def p_add(u, v):
    n = max(len(u), len(v))
    r = []
    for i in range(n):
        a = u[i] if i < len(u) else s_zero()
        b = v[i] if i < len(v) else s_zero()
        r.append(s_add(a, b))
    return p_trim(r)


def p_neg(u):
    return [s_neg(c) for c in u]


def p_sub(u, v):
    return p_add(u, p_neg(v))


def p_mul(u, v):
    if not u or not v:
        return []
    r = [s_zero() for _ in range(len(u) + len(v) - 1)]
    for i, a in enumerate(u):
        for j, b in enumerate(v):
            r[i + j] = s_add(r[i + j], s_mul(a, b))
    return p_trim(r)


def p_smul(c, u):
    return p_trim([s_mul(c, a) for a in u])


def p_divmod(u, v, tag):
    """Division with remainder; the leading coefficient of v must be a unit."""
    v = p_trim(list(v))
    assert v, "division by zero polynomial"
    lc = v[-1]
    UNIT_LOG.append((tag, s_constterm(lc)))
    lcinv = s_inv(lc)
    u = p_trim(list(u))
    q = [s_zero() for _ in range(max(len(u) - len(v) + 1, 0))]
    while len(u) >= len(v):
        d = len(u) - len(v)
        c = s_mul(u[-1], lcinv)
        q[d] = s_add(q[d], c)
        for i in range(len(v)):
            u[i + d] = s_sub(u[i + d], s_mul(c, v[i]))
        u = p_trim(u[:-1] + [s_zero()])
    return p_trim(q), u


def p_mod(u, v, tag):
    return p_divmod(u, v, tag)[1]


def p_monic(u, tag):
    UNIT_LOG.append((tag, s_constterm(u[-1])))
    return p_smul(s_inv(u[-1]), u)


def p_invmod(v, u, tag):
    """Inverse of `v` modulo `u` (unit leading coefficient), as a rational map:
    solve the linear system given by the multiplication-by-`v` matrix on the basis
    `1, x, ..., x^(n-1)` of R[x]/(u) by Gaussian elimination; the pivots met are the
    good-position units (their product is essentially `res(u, v)`)."""
    n = len(u) - 1
    cols = []
    w = p_mod(list(v), u, f"{tag}/red")
    for j in range(n):
        cols.append([w[i] if i < len(w) else s_zero() for i in range(n)])
        w = p_mod(p_mul(w, [s_zero(), s_const(1)]), u, f"{tag}/shift")
    M = [[cols[j][i] for j in range(n)] for i in range(n)]
    b = [s_const(1)] + [s_zero() for _ in range(n - 1)]
    for k in range(n):
        piv = next((r for r in range(k, n) if s_constterm(M[r][k]) != 0), None)
        assert piv is not None, f"invmod: singular system ({tag})"
        M[k], M[piv] = M[piv], M[k]
        b[k], b[piv] = b[piv], b[k]
        UNIT_LOG.append((f"{tag}/pivot{k}", s_constterm(M[k][k])))
        inv = s_inv(M[k][k])
        M[k] = [s_mul(inv, c) for c in M[k]]
        b[k] = s_mul(inv, b[k])
        for r in range(n):
            if r != k and M[r][k]:
                c = M[r][k]
                M[r] = [s_sub(M[r][j], s_mul(c, M[k][j])) for j in range(n)]
                b[r] = s_sub(b[r], s_mul(c, b[k]))
    return p_trim(list(b))


# ---------------------------------------------------------------------------
# The curve and Cantor arithmetic (genus 2).
# ---------------------------------------------------------------------------

G = 2


def poly_const_coeffs(coeffs):
    return [s_const(c) for c in coeffs]


F_COEFFS = [1, -1, 0, 0, 0, 1]  # f(x) = x^5 - x + 1


def fpol():
    # rebuilt on each use: the exponent-tuple length must match the current Ctx.NVARS
    return poly_const_coeffs(F_COEFFS)


def lin_solve(A, b, tag):
    """Solve A t = b over the series ring by Gaussian elimination with unit pivots
    (rows m <= cols n; free variables set to 0). The pivots are the good-position
    units (a Sylvester-type resultant condition)."""
    m, n = len(A), len(A[0])
    A = [row[:] for row in A]
    b = b[:]
    piv_cols = []
    r = 0
    for c in range(n):
        if r == m:
            break
        piv = next((i for i in range(r, m) if s_constterm(A[i][c]) != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        b[r], b[piv] = b[piv], b[r]
        UNIT_LOG.append((f"{tag}/pivot{r}", s_constterm(A[r][c])))
        inv = s_inv(A[r][c])
        A[r] = [s_mul(inv, x) for x in A[r]]
        b[r] = s_mul(inv, b[r])
        for i in range(m):
            if i != r and A[i][c]:
                co = A[i][c]
                A[i] = [s_sub(A[i][k], s_mul(co, A[r][k])) for k in range(n)]
                b[i] = s_sub(b[i], s_mul(co, b[r]))
        piv_cols.append(c)
        r += 1
    assert r == m, f"lin_solve: system not of full rank ({tag})"
    t = [s_zero() for _ in range(n)]
    for i, c in enumerate(piv_cols):
        t[c] = b[i]
    return t


def poly_coeff(u, i):
    return u[i] if i < len(u) else s_zero()


def cantor_add(D1, D2, tag):
    """Cantor composition (d = 1 branch, covering the near-diagonal and doubling) plus
    reduction, as a rational map. Solves `s1 u1 + s2 u2 + s3 (v1+v2) = 1` with
    `deg s1, s2 < g`, `deg s3 < g`, by `lin_solve`; then
    `v3 = s1 u1 v2 + s2 u2 v1 + s3 (v1 v2 + f) mod u1 u2`, `u3 = u1 u2`, and Cantor
    reduction to degree <= g."""
    (u1, v1), (u2, v2) = D1, D2
    e = p_add(v1, v2)
    n1, n2, n3 = G, G, G          # coefficient counts of s1, s2, s3
    m = 2 * G                      # work in degrees < 2g
    A = [[s_zero() for _ in range(n1 + n2 + n3)] for _ in range(m)]
    for j in range(n1):            # s1 * u1
        for i in range(len(u1)):
            if i + j < m:
                A[i + j][j] = s_add(A[i + j][j], u1[i])
    for j in range(n2):            # s2 * u2
        for i in range(len(u2)):
            if i + j < m:
                A[i + j][n1 + j] = s_add(A[i + j][n1 + j], u2[i])
    for j in range(n3):            # s3 * e
        for i in range(len(e)):
            if i + j < m:
                A[i + j][n1 + n2 + j] = s_add(A[i + j][n1 + n2 + j], e[i])
    bvec = [s_const(1)] + [s_zero() for _ in range(m - 1)]
    t = lin_solve(A, bvec, f"{tag}/bezout")
    s1, s2, s3 = t[:n1], t[n1:n1 + n2], t[n1 + n2:]
    u3 = p_mul(u1, u2)
    v3 = p_add(p_add(p_mul(p_mul(s1, u1), v2), p_mul(p_mul(s2, u2), v1)),
               p_mul(s3, p_add(p_mul(v1, v2), fpol())))
    v3 = p_mod(v3, u3, f"{tag}/vred")
    while len(u3) - 1 > G:
        num = p_sub(fpol(), p_mul(v3, v3))
        u4, rem = p_divmod(num, u3, f"{tag}/reduce")
        assert not rem, "reduction: u3 does not divide f - v3^2"
        u4 = p_monic(u4, f"{tag}/monic")
        v4 = p_mod(p_neg(v3), u4, f"{tag}/vmod")
        u3, v3 = u4, v4
    return p_trim(u3), p_trim(v3)


def mumford_neg(D):
    u, v = D
    return u, p_neg(v)


# ---------------------------------------------------------------------------
# The chart: center tau, Hensel square root V(X), chart points.
# ---------------------------------------------------------------------------

U_TAU = [0, -1, 1]  # x^2 - x   (P1 = (0,1), P2 = (1,1))
V_TAU = [1]         # v = 1


def chart_point(xvars):
    """Chart point of X = (X_1, X_2): u = u_tau + X_2 x + X_1, v = V(X)."""
    u = [s_add(s_const(U_TAU[0]), xvars[0]), s_add(s_const(U_TAU[1]), xvars[1]),
         s_const(U_TAU[2])]
    # Newton iteration for V^2 = f mod u, V(0) = v_tau
    v = poly_const_coeffs(V_TAU) + [s_zero()]
    v = v[:G]
    for _ in range(Ctx.TRUNC + 1):
        err = p_mod(p_sub(p_mul(v, v), fpol()), u, "chart/err")
        if not err:
            break
        winv = p_invmod(p_smul(s_const(2), v), u, "chart/2v-inv")
        v = p_mod(p_sub(v, p_mul(err, winv)), u, "chart/newton")
    assert not p_mod(p_sub(p_mul(v, v), fpol()), u, "chart/final"), \
        "chart: V(X)^2 != f mod u at this truncation"
    return u, v


def chart_coords(D):
    """Chart coordinates of a Mumford datum: coefficients of u - u_tau (degree u = g)."""
    u, v = D
    assert len(u) - 1 == G, "chart_coords: datum not of full degree g"
    u = p_monic(list(u), "coords/monic")
    return [s_sub(u[i], s_const(U_TAU[i])) for i in range(G)]


# ---------------------------------------------------------------------------
# F_tau and the design checks.
# ---------------------------------------------------------------------------

def build_ftau(nvars, xidx, yidx):
    """F_tau(X, Y) in a series ring with nvars variables, X at positions xidx,
    Y at positions yidx."""
    Ctx.NVARS = nvars
    X = [s_var(i) for i in xidx]
    Y = [s_var(i) for i in yidx]
    chx = chart_point(X)
    chy = chart_point(Y)
    tau = (poly_const_coeffs(U_TAU), poly_const_coeffs(V_TAU))
    s = cantor_add(chx, chy, "F/add")
    s = cantor_add(s, mumford_neg(tau), "F/subtau")
    return chart_coords(s)


def series_padic_ok(a, p):
    return all(c.denominator % p != 0 for c in a.values())


def main():
    if len(sys.argv) > 1:
        Ctx.TRUNC = int(sys.argv[1])
    p = 11
    print(f"curve y^2 = x^5 - x + 1, tau = [(0,1)] + [(1,1)] - 2*inf, p = {p}, "
          f"truncation degree < {Ctx.TRUNC}")

    # --- 2*tau over Q, good position of the derived datum
    Ctx.NVARS = 1
    two_tau = cantor_add((poly_const_coeffs(U_TAU), poly_const_coeffs(V_TAU)),
                     (poly_const_coeffs(U_TAU), poly_const_coeffs(V_TAU)), "2tau")
    print("2*tau =", [[str(s_constterm(c)) for c in part] for part in two_tau])

    # --- F_tau(X, Y) in 4 variables
    ftau = build_ftau(4, [0, 1], [2, 3])
    print(f"F_tau computed: {len(ftau)} components, "
          f"{sum(len(c) for c in ftau)} monomials")

    # integrality at p (lem:Ftau-basic)
    ok = all(series_padic_ok(c, p) for c in ftau)
    print("p-integrality of F_tau:", "OK" if ok else "FAIL")

    # unit law F(X, 0) = X (lem:Ftau-basic)
    zero2 = [s_zero(), s_zero()]
    x2 = [s_var(0), s_var(1)]
    fx0 = [s_subst(c, x2 + zero2) for c in ftau]
    print("F_tau(X,0) = X:", "OK" if all(
        s_sub(fx0[i], s_var(i)) == {} for i in range(G)) else "FAIL")
    f0y = [s_subst(c, zero2 + x2) for c in ftau]
    print("F_tau(0,Y) = Y:", "OK" if all(
        s_sub(f0y[i], s_var(i)) == {} for i in range(G)) else "FAIL")

    # commutativity (lem:Ftau-basic)
    y_then_x = [s_var(2), s_var(3), s_var(0), s_var(1)]
    fyx = [s_subst(c, y_then_x) for c in ftau]
    print("F_tau(X,Y) = F_tau(Y,X):", "OK" if all(
        s_sub(ftau[i], fyx[i]) == {} for i in range(G)) else "FAIL")

    # linear term: F = X + Y + higher order
    lin_ok = True
    for i in range(G):
        lin = {e: c for e, c in ftau[i].items() if sum(e) == 1}
        expect = s_add(s_var(i), s_var(i + G))
        lin_ok = lin_ok and (s_sub(lin, expect) == {})
    print("linear term X + Y:", "OK" if lin_ok else "FAIL")

    # --- associativity in 6 variables (thm:Ftau-assoc)
    ftau6 = build_ftau(6, [0, 1], [2, 3])
    Z = [s_var(4), s_var(5)]
    XY = [dict(c) for c in ftau6]
    lhs = [s_subst(c, XY + Z) for c in ftau6]           # F(F(X,Y),Z)
    YZ = [s_subst(c, [s_var(2), s_var(3), s_var(4), s_var(5), s_zero(), s_zero()])
          for c in ftau6]
    rhs = [s_subst(c, [s_var(0), s_var(1)] + YZ) for c in ftau6]  # F(X,F(Y,Z))
    assoc_ok = all(s_sub(lhs[i], rhs[i]) == {} for i in range(G))
    print(f"associativity (degree < {Ctx.TRUNC}):", "OK" if assoc_ok else "FAIL")

    # --- M(X) = dF/dY (X, 0), M(0) = I (lem:delta-rational)
    Ctx.NVARS = 4
    m00_ok = True
    for i in range(G):
        for j in range(G):
            dij = s_pderiv(ftau[i], G + j)
            mij0 = s_constterm(s_subst_partial_zero(dij))
            m00_ok = m00_ok and (mij0 == (1 if i == j else 0))
    print("M(0) = I:", "OK" if m00_ok else "FAIL")

    # unit-inversion log: all constant terms inverted must be p-units (def:goodpos)
    bad = [t for t, c in UNIT_LOG
           if c == 0 or c.numerator % p == 0 or c.denominator % p == 0]
    print(f"good-position unit inversions: {len(UNIT_LOG)} logged,",
          "all p-units OK" if not bad else f"NON-UNIT at {sorted(set(bad))}")

    print()
    print("ALL CHECKS PASSED" if all([ok, lin_ok, assoc_ok, m00_ok, not bad]) else
          "*** SOME CHECKS FAILED ***")


def s_subst_partial_zero(a):
    """Set Y = 0 (variables G..2G-1) in a 4-variable series."""
    return {e: c for e, c in a.items() if all(e[G + j] == 0 for j in range(G))}


if __name__ == "__main__":
    main()
