/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Power series of order zero

## Main statements

* `PowerSeries.order_eq_zero_of_constantCoeff_ne_zero`: a power series with nonzero constant
  coefficient has order `0`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace PowerSeries

variable {O : Type*} [CommRing O]

/-- A power series with nonzero constant coefficient has order `0`. -/
theorem order_eq_zero_of_constantCoeff_ne_zero {κ : Type*} [Semiring κ] {φ : κ⟦X⟧}
    (h : constantCoeff φ ≠ 0) : φ.order = 0 := by
  by_contra hne
  exact h (order_ne_zero_iff_constCoeff_eq_zero.mp hne)

end PowerSeries

end
