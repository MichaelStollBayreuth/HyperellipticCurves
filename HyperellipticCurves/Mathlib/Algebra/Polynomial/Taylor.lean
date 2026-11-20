/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.Algebra.Polynomial.Taylor`: `Polynomial.rootMultiplicity`, from
-- `Mathlib.Algebra.Polynomial.Div`, for the statement of `Polynomial.rootMultiplicity_taylor`.
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Taylor

-- For the proof of `Polynomial.rootMultiplicity_taylor` only:
-- `Polynomial.rootMultiplicity_comp_C_mul_X_add_C`, from `Mathlib.Algebra.Polynomial.RingDivision`.
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Root multiplicities under the Taylor shift

## Main statements

* `Polynomial.rootMultiplicity_taylor`: `rootMultiplicity z (taylor r p) =
  rootMultiplicity (z + r) p`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- Root multiplicities shift under `taylor`. -/
theorem rootMultiplicity_taylor {R : Type*} [CommRing R] (p : R[X]) (r z : R) :
    (taylor r p).rootMultiplicity z = p.rootMultiplicity (z + r) := by
  rw [taylor_apply,
    show (Polynomial.X + Polynomial.C r : R[X])
      = Polynomial.C 1 * Polynomial.X + Polynomial.C r by rw [map_one, one_mul],
    rootMultiplicity_comp_C_mul_X_add_C p 1 r z isUnit_one, one_mul]

end Polynomial

end
