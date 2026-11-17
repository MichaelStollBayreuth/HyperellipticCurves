/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Artinian.Module

/-!
# Idempotents of the reduction of an Artinian ring

## Main statements

* `IsArtinianRing.exists_isIdempotentElem_ne_zero_ne_one_of_ne`: a commutative Artinian ring with
  two distinct maximal ideals has a nontrivial idempotent in its reduction
  `B ⧸ nilradical B`, the indicator of one factor of `IsArtinianRing.quotNilradicalEquivPi`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- A commutative Artinian ring with two distinct maximal ideals has a nontrivial idempotent in
its reduction `B ⧸ nilradical B`: under the Artinian decomposition
`B ⧸ nilradical B ≃ ∏ 𝔪, B ⧸ 𝔪`, the indicator of a single factor is such an idempotent. -/
theorem IsArtinianRing.exists_isIdempotentElem_ne_zero_ne_one_of_ne {B : Type*} [CommRing B]
    [IsArtinianRing B] {M₁ M₀ : MaximalSpectrum B} (hMne : M₁ ≠ M₀) :
    ∃ e : B ⧸ nilradical B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  set φ := IsArtinianRing.quotNilradicalEquivPi B
  set v : (J : MaximalSpectrum B) → B ⧸ J.asIdeal := fun J ↦ if J = M₁ then 1 else 0 with hv
  have hvv : v * v = v := by
    funext J
    by_cases h : J = M₁ <;> simp [hv, h]
  have hv1 : v M₁ = 1 := by simp [hv]
  have hv0 : v M₀ = 0 := by simp [hv, hMne.symm]
  have hnt₁ : Nontrivial (B ⧸ M₁.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr M₁.isMaximal.ne_top
  have hnt₀ : Nontrivial (B ⧸ M₀.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr M₀.isMaximal.ne_top
  refine ⟨φ.symm v, by rw [IsIdempotentElem, ← map_mul, hvv], fun h ↦ ?_, fun h ↦ ?_⟩
  · have hv' : v = 0 := by rw [← φ.apply_symm_apply v, h, map_zero]
    exact one_ne_zero (hv1.symm.trans ((congrFun hv' M₁).trans (Pi.zero_apply M₁)))
  · have hv' : v = 1 := by rw [← φ.apply_symm_apply v, h, map_one]
    exact zero_ne_one (hv0.symm.trans ((congrFun hv' M₀).trans (Pi.one_apply M₀)))

end
