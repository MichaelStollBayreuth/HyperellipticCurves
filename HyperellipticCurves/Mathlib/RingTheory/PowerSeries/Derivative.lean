/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The derivative of power series under base change

## Main statements

* `PowerSeries.map_derivative`: the formal derivative commutes with coefficientwise base change.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace PowerSeries

variable {O : Type*} [CommRing O]

/-- The formal derivative commutes with coefficientwise base change. -/
theorem map_derivative {K : Type*} [CommRing K] (ψ : O →+* K) (s : O⟦X⟧) :
    PowerSeries.map ψ (PowerSeries.derivative s)
      = PowerSeries.derivative (PowerSeries.map ψ s) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul, map_add, map_natCast, map_one]

end PowerSeries

end
