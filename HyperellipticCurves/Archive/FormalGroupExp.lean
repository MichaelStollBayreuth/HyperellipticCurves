/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.Mathlib.RingTheory.MvPowerSeries.CompositionalInverse
public import HyperellipticCurves.Series.FormalGroupLaw.Log

/-!
# The formal exponential of a formal group law

The formal exponential `ChabautyColeman.FormalGroupLaw.exp` — the compositional inverse of
the logarithm via `MvPowerSeries.invSubst` — with the inverse identities
`log_comp_exp`/`exp_comp_log`, and the order-`≥ 2` certificate `log_sub_X_order` (with its
helper `coeff_single_log`) feeding the inverse construction. The exponential serves to prove
*injectivity* of the abelian logarithm (`HyperellipticCurves.Archive.LogInjective`), on which
the main theorems do not depend: the count uses the logarithm only as a homomorphism with
integral `π`-scaled coefficients, and the basis/independence arguments run through the trace
matrix (`ChabautyColeman.det_traceMatrix_ne_zero`) instead.

Blueprint node: `lem:fgl-exp`.
-/

@[expose] public section

open MvPowerSeries

namespace ChabautyColeman.FormalGroupLaw

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Φ : FormalGroupLaw K ι)

/-- The linear term of the logarithm is `X i`. -/
theorem coeff_single_log (i j : ι) :
    MvPowerSeries.coeff (Finsupp.single j 1) (Φ.log i) = if i = j then 1 else 0 := by
  classical
  rw [log, coeff_eulerAntideriv, map_sum]
  have hterm (l : ι) : MvPowerSeries.coeff (Finsupp.single j 1)
      (Φ.diffMatrix⁻¹ i l * MvPowerSeries.X l)
      = if l = j then constantCoeff (Φ.diffMatrix⁻¹ i l) else 0 := by
    have hX : (MvPowerSeries.X l : MvPowerSeries ι K)
        = MvPowerSeries.monomial (Finsupp.single l 1) 1 := rfl
    by_cases hl : l = j
    · subst hl
      rw [ite_eq_left rfl, hX, MvPowerSeries.coeff_mul_monomial, ite_eq_left le_rfl]
      simp
    · rw [ite_eq_right hl, hX, MvPowerSeries.coeff_mul_monomial, ite_eq_right]
      intro hle
      have h1 := Finsupp.le_def.mp hle l
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hl] at h1
      exact absurd h1 (by lia)
  rw [Finset.sum_congr rfl fun l _ ↦ hterm l,
    Finset.sum_ite_eq' Finset.univ j (fun l ↦ constantCoeff (Φ.diffMatrix⁻¹ i l)),
    ite_eq_left (Finset.mem_univ j)]
  have h2 : (Φ.diffMatrix⁻¹.map (constantCoeff (R := K))) i j
      = (1 : Matrix ι ι K) i j := by
    rw [Φ.diffMatrixInv_map_constantCoeff]
  rw [Matrix.map_apply, Matrix.one_apply] at h2
  rw [h2]
  simp [Finsupp.degree_single]

/-- The logarithm has zero constant term and identity linear part, so `Λ i - X i` has
order `≥ 2`. -/
theorem log_sub_X_order (i : ι) (e : ι →₀ ℕ) (he : e.degree ≤ 1) :
    coeff e (Φ.log i - X i) = 0 := by
  rw [map_sub]
  rcases Nat.lt_or_ge e.degree 1 with h | h
  · have h0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by lia)
    subst h0
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      Φ.constantCoeff_log, constantCoeff_X, sub_zero]
  · have he1 : e.degree = 1 := by lia
    obtain ⟨j, rfl⟩ : ∃ j, e = Finsupp.single j 1 := by
      have hne0 : e ≠ 0 := by intro h0; rw [h0, map_zero] at he1; simp at he1
      obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne0
      refine ⟨j, ?_⟩
      have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
      have hejle : e j ≤ 1 := he1 ▸ Finsupp.le_degree j e
      ext s
      rcases eq_or_ne s j with rfl | hs
      · rw [Finsupp.single_eq_same]; lia
      · rw [Finsupp.single_eq_of_ne hs]
        by_contra hne
        have hsum : e j + e s ≤ e.degree := by
          have hsub : ({j, s} : Finset ι) ⊆ e.support := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hj
            · exact Finsupp.mem_support_iff.mpr hne
          calc e j + e s = ∑ x ∈ ({j, s} : Finset ι), e x := (Finset.sum_pair (Ne.symm hs)).symm
            _ ≤ ∑ x ∈ e.support, e x := Finset.sum_le_sum_of_subset hsub
            _ = e.degree := (Finsupp.degree_apply e).symm
        lia
    rw [Φ.coeff_single_log, coeff_X]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [ite_eq_right hij,
        ite_eq_right (fun h ↦ hij (Finsupp.single_left_injective one_ne_zero h).symm), sub_zero]

/-- The formal exponential of a formal group law: the compositional inverse of the
logarithm. -/
noncomputable def exp (i : ι) : MvPowerSeries ι K := invSubst Φ.log i

/-- `Λ ∘ Exp = X`: the logarithm composed with the exponential is the identity. -/
theorem log_comp_exp (i : ι) : subst Φ.exp (Φ.log i) = X i :=
  subst_invSubst (log_sub_X_order Φ) i

/-- `Exp ∘ Λ = X`: the exponential composed with the logarithm is the identity. -/
theorem exp_comp_log (i : ι) : subst Φ.log (Φ.exp i) = X i :=
  subst_a_invSubst (log_sub_X_order Φ) i

end ChabautyColeman.FormalGroupLaw

end
