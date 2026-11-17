/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.PowerSeries.Order

/-!
# `PowerSeries.rescale` by a unit preserves the order

## Main statements

* `ChabautyColeman.order_rescale_of_isUnit`: `order (rescale c g) = order g` for a unit `c`.

Its clients are those of `ChabautyColeman.rescale_aeval`, in the Archive.

Auxiliary material for the Archive of the formalization of the Chabauty–Coleman bound for
hyperelliptic curves (the main theorems do not depend on it); an upstreaming candidate for
Mathlib.
-/

@[expose] public section

open Polynomial PowerSeries

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

/-- `order` is preserved under `rescale` by a unit. -/
theorem order_rescale_of_isUnit {c : O} (hc : IsUnit c) (g : O⟦X⟧) :
    (rescale c g).order = g.order := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  set n := g.order.toNat
  have hgord : g.order = (n : ℕ∞) :=
    (ENat.natCast_toNat (order_finite_iff_ne_zero.mpr hg).ne).symm
  obtain ⟨hc0, hlt⟩ := order_eq_nat.mp hgord
  rw [hgord, order_eq_nat]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [coeff_rescale, ne_eq, (hc.pow n).mul_right_eq_zero]; exact hc0
  · rw [coeff_rescale, hlt i hi, mul_zero]

end ChabautyColeman

end
