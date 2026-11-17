/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The units of the fraction field of a discrete valuation ring

## Main statements

* `IsDiscreteValuationRing.unitsEquivProd`: `Kˣ ≃* ℤ × Rˣ` for the fraction field `K`, by
  `ϖ ^ n * u ↦ (n, u)` for a uniformizer `ϖ`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

open Ideal IsLocalRing
open scoped Pointwise

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section FractionRing

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}

private lemma eq_zero_and_eq_one_of_zpow_mul_eq_one (hϖ : Irreducible ϖ) {n : ℤ} {u : Rˣ}
    (h : algebraMap R K ϖ ^ n * algebraMap R K u = 1) : n = 0 ∧ u = 1 := by
  have hϖ0 : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  rw [← Int.toNat_sub_toNat_neg n, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast, div_mul_eq_mul_div,
    div_eq_one_iff_eq (pow_ne_zero _ hϖ0)] at h
  have h' : (u : R) * ϖ ^ n.toNat = (1 : Rˣ) * ϖ ^ (-n).toNat :=
    IsFractionRing.injective R K (by simpa [mul_comm] using h)
  exact ⟨by lia [unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ h'], unit_mul_pow_congr_unit hϖ _ _ _ _ h'⟩

variable {K} in
/-- Every unit of the fraction field `K` of a discrete valuation ring `R` is `ϖ ^ n * u` for a
unique `n : ℤ` and a unique unit `u` of `R`, for a uniformizer `ϖ`. Existence is
`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible`. -/
theorem bijective_zpowersHom_coprod_unitsMap (hϖ : Irreducible ϖ) (hϖ0 : algebraMap R K ϖ ≠ 0) :
    Function.Bijective ((zpowersHom Kˣ (Units.mk0 _ hϖ0)).coprod
      (Units.map (algebraMap R K : R →* K))) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun ⟨n, u⟩ h ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨hn, rfl⟩ := eq_zero_and_eq_one_of_zpow_mul_eq_one K hϖ (n := n.toAdd) (u := u)
      (by simpa using congr(Units.val $h))
    exact Prod.ext (toAdd_eq_zero.mp hn) rfl
  · obtain ⟨n, u, hx⟩ := exists_units_eq_smul_zpow_of_irreducible hϖ x.ne_zero
    exact ⟨(.ofAdd n, u), Units.ext (by simp [hx, Units.smul_def, Algebra.smul_def, mul_comm])⟩

/-- The isomorphism `Kˣ ≃* ℤ × Rˣ` (with `ℤ` written multiplicatively) inverse to
`(n, u) ↦ ϖ ^ n * u`, for a uniformizer `ϖ` of a discrete valuation ring `R` with fraction field
`K` (`IsDiscreteValuationRing.bijective_zpowersHom_coprod_unitsMap`). -/
noncomputable def unitsEquivProd (hϖ : Irreducible ϖ) : Kˣ ≃* Multiplicative ℤ × Rˣ :=
  have hϖ0 : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero
  (MulEquiv.ofBijective _ (bijective_zpowersHom_coprod_unitsMap hϖ hϖ0)).symm

theorem val_unitsEquivProd_symm_apply (hϖ : Irreducible ϖ) (n : Multiplicative ℤ) (u : Rˣ) :
    ((unitsEquivProd K hϖ).symm (n, u) : K) = algebraMap R K ϖ ^ n.toAdd * algebraMap R K u := by
  simp [unitsEquivProd]

variable {K} in
theorem unitsEquivProd_apply_of_val_eq (hϖ : Irreducible ϖ) {x : Kˣ} {n : ℤ} {u : Rˣ}
    (hx : (x : K) = algebraMap R K ϖ ^ n * algebraMap R K u) :
    unitsEquivProd K hϖ x = (.ofAdd n, u) :=
  (MulEquiv.eq_symm_apply _).mp (Units.ext (by rw [val_unitsEquivProd_symm_apply, hx, toAdd_ofAdd]))

end FractionRing

end IsDiscreteValuationRing
