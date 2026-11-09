# Prototype scripts

Symbolic and numerical checks, at small genus, of statements in the blueprint and in the Lean
sources. They are independent of the formalization: each script recomputes the objects from
scratch and reports or asserts the claimed identities. The `.m` files are
[Magma](https://magma.maths.usyd.edu.au/) scripts, run as `magma -b G:=3 script.m` (the genus
`G` and further options are set on the command line, see the header of each script); the `.py`
files need only Python 3 and its standard library.

## The witness for all genera (blueprint chapter 4, the point-by-point fold)

- `symfold.m` — the fold `τ + τ − τ` computed symbolically on the cuspidal curve
  `y² = x^(2g+1)` at `g` generic points, with every step condition and its integer content.
- `apic.m` — the moment characterization of the states of the fold (blueprint
  `thm:cusp-moment`), compared with the fold computed by Cantor's algorithm.
- `p1lemmas.m` — the chain of lemmas behind the moment characterization.
- `revfold.m` — the mirror: the second phase of the fold retraces the first (blueprint
  `lem:fold-mirror`).
- `detcond.m` — every condition of the fold computed from the moment determinants alone,
  without running the fold; used to certify all conditions for genus `≤ 6`.
- `tracefold.m` — the invariance of the trace form along the fold, at genus 2 and 3
  (`HyperellipticCurves/Log/Fold/FoldTrace.lean`).

## The Schur-polynomial interpretation of the atoms (blueprint, remark `rem:schur-atoms`)

- `schurid.m`, `p2shapes.m` — the Cramer data of the moment system as Schur and skew Schur
  polynomials, each checked against an independent expansion.
- `branch.m` — the numerator of a fold state as a single Schur polynomial of the extended
  alphabet.
- `p34atoms.m` — the condition atoms as single Schur values, with their integer contents and
  extreme coefficients, the candidates for the certificates.
- `c3check.m` — the first peeling step for the atoms with a negated point.

## Genus 2 (blueprint chapter 4)

- `g2_formal_group.py` — Cantor's algorithm as a rational map, the chart at `τ` and the
  translated formal group law `F_τ` for `y² = x⁵ − x + 1` at `p = 11`, with integrality, the
  unit laws, commutativity, associativity and `M(0) = I` checked up to a given total degree; its
  design note explains why Cantor composition takes a three-term Bézout certificate
  (`HyperellipticCurves/Log/Cantor/CantorAdd.lean`, blueprint remark `rem:g2-cert`).
- `g2_omega_prime.py` — building on `g2_formal_group.py`: the logarithm of `F_τ`, the map from a
  residue disk to the chart, and the differentials `ω′_i`, with the regularity and basis
  properties of blueprint `thm:omega-prime-global`
  (`HyperellipticCurves/Log/Charts/PhiChart.lean`).
