/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The class number theorem and principal ideal rings of small discriminant

## Main statements

* `NumberField.instFiniteClassGroupIntegralClosure`: the class group of the integral closure of `ℤ`
  in `K` is finite, for any `ℤ`-algebra structure on `K`.
* `NumberField.isPrincipalIdealRing_integralClosure_iff`: the integral closure of `ℤ` in `K` is a
  principal ideal ring iff `𝓞 K` is.
* `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le`: a cubic number field
  with `|discr K| ≤ 49` has a principal ring of integers (in the root namespace `RingOfIntegers`,
  as Mathlib's `NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`).

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

open Module NumberField NumberField.InfinitePlace

namespace NumberField

/-- The **class number theorem** for the integral closure of `ℤ` in a number field `K`, for any
`ℤ`-algebra structure on `K`: as `Algebra ℤ K` is a subsingleton, it is `𝓞 K`. The generality is
needed, as `AdjoinRoot g` carries a `ℤ`-algebra structure of its own, which is not reducibly
`Ring.toIntAlgebra`. -/
instance instFiniteClassGroupIntegralClosure {K : Type*} [Field K] [NumberField K]
    [Algebra ℤ K] : Finite (ClassGroup (integralClosure ℤ K)) := by
  obtain rfl := Subsingleton.elim ‹Algebra ℤ K› (Ring.toIntAlgebra K)
  exact inferInstanceAs (Finite (ClassGroup (𝓞 K)))

/-- The integral closure of `ℤ` in a number field `K` is a principal ideal ring iff `𝓞 K` is, for
any `ℤ`-algebra structure on `K`: as `Algebra ℤ K` is a subsingleton, it is `𝓞 K`. -/
theorem isPrincipalIdealRing_integralClosure_iff {K : Type*} [Field K] [Algebra ℤ K] :
    IsPrincipalIdealRing (integralClosure ℤ K) ↔ IsPrincipalIdealRing (𝓞 K) := by
  obtain rfl := Subsingleton.elim ‹Algebra ℤ K› (Ring.toIntAlgebra K)
  rfl

end NumberField

namespace RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- A cubic number field with `|discr K| ≤ 49` has a principal ring of integers: its Minkowski
bound is less than `2` for either signature. -/
theorem isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le (h3 : finrank ℚ K = 3)
    (hd : |discr K| ≤ 49) : IsPrincipalIdealRing (𝓞 K) := by
  have hs : nrComplexPlaces K ≤ 1 := by lia [card_add_two_mul_card_eq_rank K]
  have hd' : ((|discr K| : ℤ) : ℝ) ≤ 49 := mod_cast hd
  refine NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt (hd'.trans_lt ?_)
  rw [h3]
  interval_cases nrComplexPlaces K
  · norm_num
  · norm_num
    calc (49 : ℝ) < (2 * (3.14 / 4) * (9 / 2)) ^ 2 := by norm_num
      _ < _ := by gcongr; exact Real.pi_gt_d2

end RingOfIntegers
