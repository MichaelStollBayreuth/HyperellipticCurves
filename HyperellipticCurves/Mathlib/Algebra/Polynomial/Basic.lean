/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Basic

/-!
# A unit `2` stays a unit in the polynomial ring

## Main statements

* `Polynomial.isUnit_two`: if `2` is a unit of `R`, it is a unit of `R[X]`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- A unit `2` of the base ring stays a unit in the polynomial ring, as the constant `C 2`. -/
theorem isUnit_two {R : Type*} [CommRing R] (h : IsUnit (2 : R)) : IsUnit (2 : R[X]) := by
  rw [← map_ofNat (C : R →+* R[X]) 2]
  exact h.map C

end Polynomial

end
