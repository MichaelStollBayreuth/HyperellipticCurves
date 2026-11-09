/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Series.FormalGroupLaw.Basic
public import HyperellipticCurves.Series.FormalGroupLaw.Invariance
public import HyperellipticCurves.Series.FormalGroupLaw.Log

/-!
# Formal group laws

`ChabautyColeman.FormalGroupLaw O ι` is an `ι`-dimensional commutative formal group law
over `O`: a family of power series `F i` in two blocks of `ι` variables with
`F(X,0) = X`, `F(0,Y) = Y`, `F(X,Y) = F(Y,X)` and `F(F(X,Y),Z) = F(X,F(Y,Z))`, the
substitutions being Mathlib's formal `MvPowerSeries.subst`. (Mathlib's `FormalGroup` is
one-dimensional with points valued in power series rings; here arbitrary finite
dimension is needed, and the group laws are evaluated at points of the maximal ideal.)

The development is split across the files re-exported here:
* `HyperellipticCurves.Series.FormalGroupLaw.Basic` — the structure, the differential (Jacobian)
  matrix at the origin, and base change along a ring homomorphism;
* `HyperellipticCurves.Series.FormalGroupLaw.Invariance` — closedness of the invariant differential
  (`pderiv_diffMatrixInv_symm`), the technical heart of the logarithm construction;
* `HyperellipticCurves.Series.FormalGroupLaw.Log` — the formal logarithm `log` (radial
  antiderivative of the invariant differential), with its `p`-adic denominator estimates.

(The formal exponential and the packaged `𝔪`-points monoid are formalized in
`HyperellipticCurves.Archive.FormalGroupExp` and `HyperellipticCurves.Archive.FormalGroupPoints`;
the main theorems do not depend on them.)

Blueprint nodes: `def:fgl`, `def:fgl-diff`, `def:fgl-log`.
-/
