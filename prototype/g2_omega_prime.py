#!/usr/bin/env python3
"""Genus-2 prototype for `def:phiD` and `thm:omega-prime-global`.

Builds on g2_formal_group.py (curve y^2 = x^5 - x + 1, tau = [(0,1)]+[(1,1)]-2*inf,
p = 11). Validates, symbolically over Q with exact arithmetic:

* the FGL logarithm `L` of `F_tau`, constructed by Euler-integrating the invariant
  differential matrix `N(X) = M(X)^{-1}`, `M = dF/dY(X,0)`; functional equation
  `L(F(X,Y)) = L(X) + L(Y)` checked to the truncation (validates closedness of the
  rows of `N` and `def:Lam`-side theory);
* the curve-to-chart map (`def:phiD`): for a residue disk with center `P0` and an
  auxiliary point `Q`, the datum of `[P_z] - [P0] + tau` computed as
  `([P_z + iota Q - 2 inf]) + ([Q + iota P0 - 2 inf]) + tau` through Cantor
  arithmetic as a rational map — every inverted quantity logged and checked to be a
  p-unit (the good-locus design of `def:phiD`);
* `omega'_i` on the disk: the z-expansion `sum_j N_ij(zeta(z)) zeta_j'(z)`, checked
  equal to `d/dz L_i(zeta(z))` (the chain-rule identity behind (b));
* independence of the auxiliary `Q` (`thm:omega-prime-global`(a)): the expansions
  agree for different auxiliary points;
* regularity and basis (`thm:omega-prime-global`(c)): the expansions are p-integral,
  and on each disk `omega'_i = a_i1 (dx/y) + a_i2 (x dx/y)` exactly, with the SAME
  rational 2x2 matrix `A` on different disks, invertible with p-unit determinant.

Run: `python3 g2_omega_prime.py [truncation_degree]` (default 6).
"""

import sys
from fractions import Fraction

import g2_formal_group as GG
from g2_formal_group import (Ctx, UNIT_LOG, G, U_TAU, V_TAU, F_COEFFS,
                             s_zero, s_const, s_var, s_add, s_neg, s_sub, s_mul,
                             s_smul, s_constterm, s_inv, s_subst, s_pderiv,
                             poly_const_coeffs, cantor_add, chart_coords, build_ftau)

P = 11


def horner(x):
    r = s_zero()
    for c in reversed(F_COEFFS):
        r = s_add(s_mul(r, x), s_const(c))
    return r


def disk_point(x0, y0):
    """The disk parametrization x = x0 + z, y = y(z) with y(0) = y0 (1 variable)."""
    x = s_add(s_const(x0), s_var(0))
    fx = horner(x)
    y = s_const(y0)
    for _ in range(Ctx.TRUNC + 2):
        err = s_sub(s_mul(y, y), fx)
        if not err:
            break
        y = s_sub(y, s_mul(err, s_inv(s_smul(2, y))))
    assert s_sub(s_mul(y, y), fx) == {}, "disk: Newton did not converge"
    return x, y


def pair_datum(x1, y1, x2, y2):
    """Mumford datum of [pt1 + pt2 - 2*inf] (x1 - x2 a unit)."""
    u = [s_mul(x1, x2), s_neg(s_add(x1, x2)), s_const(1)]
    m = s_mul(s_sub(y2, y1), s_inv(s_sub(x2, x1)))
    UNIT_LOG.append(("pair/x-sep", s_constterm(s_sub(x2, x1))))
    v0 = s_sub(y1, s_mul(m, x1))
    return u, [v0, m]


def zeta(x, y, x0, y0, xq, yq, tag):
    """Chart coordinates of `[P_z] - [P0] + tau`, computed through the auxiliary `Q`:
    `([P_z + iota Q - 2inf]) + ([Q + iota P0 - 2inf]) + tau`."""
    d1 = pair_datum(x, y, s_const(xq), s_const(-yq))
    d2 = pair_datum(s_const(xq), s_const(yq), s_const(x0), s_const(-y0))
    tau = (poly_const_coeffs(U_TAU), poly_const_coeffs(V_TAU))
    s = cantor_add(d1, tau, f"{tag}/add1")
    s = cantor_add(s, d2, f"{tag}/add2")
    z = chart_coords(s)
    assert all(s_constterm(c) == 0 for c in z), f"{tag}: not centered at tau"
    return z


def reindex_to_2vars(a):
    """A 4-variable series supported on the first two variables, as a 2-var series."""
    r = {}
    for e, c in a.items():
        assert e[2] == 0 and e[3] == 0
        r[(e[0], e[1])] = c
    return r


def fgl_log(ftau):
    """The FGL logarithm from the invariant differential matrix, by Euler integration:
    `L_i` has coefficient `R_i(e)/|e|` where `R_i = sum_j N_ij X_j`, `N = M^{-1}`."""
    Ctx.NVARS = 4
    M = [[reindex_to_2vars({e: c for e, c in s_pderiv(ftau[i], G + j).items()
                            if e[2] == 0 and e[3] == 0})
          for j in range(G)] for i in range(G)]
    Ctx.NVARS = 2
    det = s_sub(s_mul(M[0][0], M[1][1]), s_mul(M[0][1], M[1][0]))
    dinv = s_inv(det)
    N = [[s_mul(dinv, M[1][1]), s_neg(s_mul(dinv, M[0][1]))],
         [s_neg(s_mul(dinv, M[1][0])), s_mul(dinv, M[0][0])]]
    L = []
    for i in range(G):
        R = s_add(s_mul(N[i][0], s_var(0)), s_mul(N[i][1], s_var(1)))
        L.append({e: c / sum(e) for e, c in R.items()})
    return L, N


def omega_prime(zt, N):
    """`omega'` on the disk: `sum_j N_ij(zeta(z)) * zeta_j'(z)` (1 variable)."""
    dz = [s_pderiv(c, 0) for c in zt]
    r = []
    for i in range(G):
        Ctx.NVARS = 1
        acc = s_zero()
        for j in range(G):
            Nij = N[i][j]
            # substitute the 1-variable series zeta into the 2-variable entry
            term = s_zero()
            for e, c in Nij.items():
                t = s_const(c)
                for k in range(e[0]):
                    t = s_mul(t, zt[0])
                for k in range(e[1]):
                    t = s_mul(t, zt[1])
                term = s_add(term, t)
            acc = s_add(acc, s_mul(term, dz[j]))
        r.append(acc)
    return r


def compose_log(L, zt):
    """`L_i(zeta(z))` (1 variable)."""
    r = []
    for i in range(G):
        acc = s_zero()
        for e, c in L[i].items():
            t = s_const(c)
            for k in range(e[0]):
                t = s_mul(t, zt[0])
            for k in range(e[1]):
                t = s_mul(t, zt[1])
            acc = s_add(acc, t)
        r.append(acc)
    return r


def coeff(a, n):
    return a.get((n,), Fraction(0))


def eq_upto(a, b, d):
    """Equality of 1-variable series up to degree `d` inclusive."""
    return all(coeff(a, n) == coeff(b, n) for n in range(d + 1))


def padic_ok(a):
    return all(c.denominator % P != 0 for c in a.values())


def main():
    if len(sys.argv) > 1:
        Ctx.TRUNC = int(sys.argv[1])
    else:
        Ctx.TRUNC = 6
    print(f"curve y^2 = x^5 - x + 1, tau = [(0,1)]+[(1,1)]-2*inf, p = {P}, "
          f"truncation degree < {Ctx.TRUNC}")

    # --- F_tau and the logarithm
    ftau = build_ftau(4, [0, 1], [2, 3])
    L, N = fgl_log(ftau)
    print("FGL log constructed (Euler integration of M(X)^{-1})")

    # functional equation L(F(X,Y)) = L(X) + L(Y)
    Ctx.NVARS = 4
    ok_log = True
    for i in range(G):
        lhs = s_zero()
        for e, c in L[i].items():
            t = s_const(c)
            for k in range(e[0]):
                t = s_mul(t, ftau[0])
            for k in range(e[1]):
                t = s_mul(t, ftau[1])
            lhs = s_add(lhs, t)
        rhs = s_zero()
        for e, c in L[i].items():
            t = s_const(c)
            for k in range(e[0]):
                t = s_mul(t, s_var(0))
            for k in range(e[1]):
                t = s_mul(t, s_var(1))
            rhs = s_add(rhs, t)
        for e, c in L[i].items():
            t = s_const(c)
            for k in range(e[0]):
                t = s_mul(t, s_var(2))
            for k in range(e[1]):
                t = s_mul(t, s_var(3))
            rhs = s_add(rhs, t)
        ok_log = ok_log and (s_sub(lhs, rhs) == {})
    print("L(F(X,Y)) = L(X) + L(Y):", "OK" if ok_log else "FAIL")

    # --- disks and auxiliary points
    # only x0 = -1 gives rational disk centers clear of supp(tau) and its involution;
    # (-1, 1) and (-1, -1) are distinct residue disks mod p
    disks = [((-1, 1), [(0, -1), (1, -1)]),   # center P0; two auxiliary Q's each
             ((-1, -1), [(0, -1), (1, -1)])]
    D = Ctx.TRUNC - 3  # reliable z-degree for composed/differentiated series
    A_matrices = []
    ok_all = ok_log
    for (x0, y0), quads in disks:
        Ctx.NVARS = 1
        x, y = disk_point(x0, y0)
        omegas = []
        for (xq, yq) in quads:
            zt = zeta(x, y, x0, y0, xq, yq, f"phi({x0},{y0})/Q=({xq},{yq})")
            om = omega_prime(zt, N)
            # chain-rule identity: omega' = d/dz L(zeta)
            Lz = compose_log(L, zt)
            chain_ok = all(eq_upto(s_pderiv(Lz[i], 0), om[i], D) for i in range(G))
            print(f"disk ({x0},{y0}), Q=({xq},{yq}): chain rule d/dz L(zeta) = omega':",
                  "OK" if chain_ok else "FAIL")
            ok_all = ok_all and chain_ok
            omegas.append(om)
        q_ok = all(eq_upto(omegas[0][i], omegas[1][i], D) for i in range(G))
        print(f"disk ({x0},{y0}): auxiliary-independence omega'(Q1) = omega'(Q2):",
              "OK" if q_ok else "FAIL")
        ok_all = ok_all and q_ok
        om = omegas[0]
        int_ok = all(padic_ok(om[i]) for i in range(G))
        print(f"disk ({x0},{y0}): p-integrality of omega'-expansions:",
              "OK" if int_ok else "FAIL")
        ok_all = ok_all and int_ok
        # basis identification: omega'_i = a_i1 * (1/y) + a_i2 * (x/y)
        e1 = s_inv(y)
        e2 = s_mul(x, e1)
        A = []
        basis_ok = True
        for i in range(G):
            det = coeff(e1, 0) * coeff(e2, 1) - coeff(e2, 0) * coeff(e1, 1)
            ai1 = (coeff(om[i], 0) * coeff(e2, 1) - coeff(e2, 0) * coeff(om[i], 1)) / det
            ai2 = (coeff(e1, 0) * coeff(om[i], 1) - coeff(om[i], 0) * coeff(e1, 1)) / det
            comb = s_add(s_smul(ai1, e1), s_smul(ai2, e2))
            basis_ok = basis_ok and eq_upto(om[i], comb, D)
            A.append([ai1, ai2])
        print(f"disk ({x0},{y0}): omega' in span(dx/y, x dx/y) exactly:",
              "OK" if basis_ok else "FAIL", " A =", [[str(c) for c in r] for r in A])
        ok_all = ok_all and basis_ok
        A_matrices.append(A)
    same_A = A_matrices[0] == A_matrices[1]
    print("same transition matrix A on both disks (global rational differential):",
          "OK" if same_A else "FAIL")
    ok_all = ok_all and same_A
    detA = A_matrices[0][0][0] * A_matrices[0][1][1] - A_matrices[0][0][1] * A_matrices[0][1][0]
    unit_det = detA != 0 and detA.numerator % P != 0 and detA.denominator % P != 0
    print(f"det A = {detA}: nonzero p-unit (basis of regular differentials):",
          "OK" if unit_det else "FAIL")
    ok_all = ok_all and unit_det
    bad = [t for t, c in UNIT_LOG
           if c == 0 or c.numerator % P == 0 or c.denominator % P == 0]
    print(f"unit inversions: {len(UNIT_LOG)} logged,",
          "all p-units OK" if not bad else f"NON-UNIT at {sorted(set(bad))}")
    ok_all = ok_all and not bad
    print()
    print("ALL CHECKS PASSED" if ok_all else "*** SOME CHECKS FAILED ***")


if __name__ == "__main__":
    main()
