/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Normalizing a polynomial to be monic does not change what it divides

## Main statements

* `Polynomial.mul_leadingCoeff_inv_dvd_iff`: `u * C u.leadingCoeff⁻¹ ∣ w ↔ u ∣ w` for `u ≠ 0`
  (the monic normalization of `Polynomial.monic_mul_leadingCoeff_inv`).

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- Scaling a nonzero polynomial to be monic does not change what it divides. -/
theorem mul_leadingCoeff_inv_dvd_iff {K : Type*} [Field K] {u w : K[X]} (hu : u ≠ 0) :
    u * C u.leadingCoeff⁻¹ ∣ w ↔ u ∣ w :=
  (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (inv_ne_zero (leadingCoeff_ne_zero.mpr hu)))).mul_right_dvd

end Polynomial

end
