/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

import HyperellipticCurves.Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Dirichlet's unit theorem: consequences

## Main statements

* `NumberField.Units.finrank_add_nrComplexPlaces_add_one`: `r + r₂ + 1 = [K : ℚ]`.
* `NumberField.instIsMulFGUnitsIntegralClosure`: the units of the integral closure of `ℤ` in `K`
  are finitely generated, for any `ℤ`-algebra structure on `K`.
* `NumberField.Units.finrank_eq_one_of_finrank_eq_three_of_discr_neg`: the unit rank of a cubic
  field of negative discriminant is `1`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

open Module NumberField.InfinitePlace

namespace NumberField

/-- The rank of the unit group of the integral closure of `ℤ` in `K` is that of `𝓞 K`, for any
`ℤ`-algebra structure on `K`: as `Algebra ℤ K` is a subsingleton, it is `𝓞 K`. -/
theorem finrank_additive_units_integralClosure {K : Type*} [Field K] [Algebra ℤ K] :
    finrank ℤ (Additive (integralClosure ℤ K)ˣ) = finrank ℤ (Additive (𝓞 K)ˣ) := by
  obtain rfl := Subsingleton.elim ‹Algebra ℤ K› (Ring.toIntAlgebra K)
  rfl

variable (K : Type*) [Field K] [NumberField K]

/-- **Dirichlet's unit theorem** in the form `r + r₂ + 1 = [K : ℚ]`, for the rank `r` of the unit
group and the number `r₂` of complex places. -/
theorem Units.finrank_add_nrComplexPlaces_add_one :
    finrank ℤ (Additive (𝓞 K)ˣ) + nrComplexPlaces K + 1 = finrank ℚ K := by
  rw [Units.finrank_eq, Units.rank, ← card_add_two_mul_card_eq_rank]
  lia [Fintype.card_pos (α := InfinitePlace K), card_eq_nrRealPlaces_add_nrComplexPlaces K]

variable {K}

/-- **Dirichlet's unit theorem** (finite generation) for the integral closure of `ℤ` in `K`, for any
`ℤ`-algebra structure on `K`: as `Algebra ℤ K` is a subsingleton, it is `𝓞 K`. The generality is
needed, as `AdjoinRoot g` carries a `ℤ`-algebra structure of its own, which is not reducibly
`Ring.toIntAlgebra`. -/
instance instIsMulFGUnitsIntegralClosure [Algebra ℤ K] : IsMulFG (integralClosure ℤ K)ˣ := by
  obtain rfl := Subsingleton.elim ‹Algebra ℤ K› (Ring.toIntAlgebra K)
  exact inferInstanceAs (IsMulFG (𝓞 K)ˣ)

/-- A cubic number field with negative discriminant has unit rank `1`: its signature is `(1, 1)`.
-/
theorem Units.finrank_eq_one_of_finrank_eq_three_of_discr_neg (h3 : finrank ℚ K = 3)
    (hd : discr K < 0) : finrank ℤ (Additive (𝓞 K)ˣ) = 1 := by
  obtain ⟨k, hk⟩ := (discr_neg_iff_odd_nrComplexPlaces K).mp hd
  lia [finrank_add_nrComplexPlaces_add_one K, card_add_two_mul_card_eq_rank K]

end NumberField
