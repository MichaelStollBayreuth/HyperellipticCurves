/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# The discriminant of a number field and of integral bases

## Main statements

* `NumberField.exists_eq_discr_mul_sq`: the discriminant of a `ℚ`-basis of integral elements of `K`
  is `NumberField.discr K` times a square.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

open Module

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The discriminant of a `ℚ`-basis of `K` of integral elements is the discriminant of `K` times
the square of an integer, the determinant of the integral change of basis from
`NumberField.integralBasis`. In particular `NumberField.discr K` divides it and has the same sign.
For any `ℚ`-algebra structure on `K`; they all agree, but `AdjoinRoot g` carries one of its own
(and so its power basis), which is not reducibly `DivisionRing.toRatAlgebra`. -/
theorem exists_eq_discr_mul_sq [Algebra ℚ K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) {d : ℤ} (hd : Algebra.discr ℚ b = d) :
    ∃ q : ℤ, d = discr K * q ^ 2 := by
  obtain rfl := Subsingleton.elim ‹Algebra ℚ K› (DivisionRing.toRatAlgebra)
  let b₀ := (integralBasis K).reindex ((integralBasis K).indexEquiv b)
  have hP (i j : ι) : IsIntegral ℤ (b₀.toMatrix b i j) := by
    rw [Basis.toMatrix_apply, Basis.repr_reindex_apply,
      ← IsIntegralClosure.algebraMap_mk' (𝓞 K) (b j) (hb j), integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hP)
  refine ⟨q, Int.cast_injective (α := ℚ) ?_⟩
  rw [← hd, ← b₀.toMatrix_map_vecMul b, Algebra.discr_of_matrix_vecMul, Basis.coe_reindex,
    Algebra.discr_reindex, ← coe_discr, ← hq, eq_intCast]
  push_cast
  ring

end NumberField
