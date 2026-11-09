/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Log.Cantor.CantorPipeline

/-!
# Generic degree bookkeeping for the Cantor pipeline

The degree helpers shared by the pipeline consumers: the generic cofactor degree bound
(`ChabautyColeman.ftauKBound`, `ChabautyColeman.natDegree_cofactor_le_of_sq_sub`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Helpers

variable {R : Type*} [CommRing R] {f u v : R[X]}

/-- The generic cofactor degree bound, as the `w`-degree bound of the three-block family
rings built on a curve polynomial `f` and datum degree `n`. -/
def ftauKBound (f : R[X]) (n : ℕ) : ℕ := max (2 * (n - 1)) f.natDegree - n

/-- Degree bound for the cofactor in a curve relation. -/
theorem natDegree_cofactor_le_of_sq_sub {w : R[X]} (hu : u.Monic)
    (hv : v.degree < (u.natDegree : WithBot ℕ)) (hw : v ^ 2 - f = u * w) :
    w.natDegree ≤ max (2 * (u.natDegree - 1)) f.natDegree - u.natDegree := by
  rcases eq_or_ne w 0 with rfl | h0
  · simp
  have hlc : u.leadingCoeff * w.leadingCoeff ≠ 0 := by
    rw [hu.leadingCoeff, one_mul]
    exact leadingCoeff_ne_zero.mpr h0
  have hnd : u.natDegree + w.natDegree = (v ^ 2 - f).natDegree := by rw [hw, natDegree_mul' hlc]
  have hle : (v ^ 2 - f).natDegree ≤ max (2 * (u.natDegree - 1)) f.natDegree := by
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [zero_pow two_ne_zero, zero_sub, natDegree_neg]
      exact le_max_right ..
    · have hvle : v.natDegree ≤ u.natDegree - 1 := by lia [(natDegree_lt_iff_degree_lt hv0).mpr hv]
      refine (natDegree_sub_le _ _).trans (max_le_max ?_ le_rfl)
      exact natDegree_pow_le.trans (by lia)
  lia

/-- A `natDegree` bound gives the strict `degree` bound used by the family rings. -/
theorem degree_lt_add_one_of_natDegree_le {p : R[X]} {k : ℕ} (h : p.natDegree ≤ k) :
    p.degree < (k : WithBot ℕ) + 1 :=
  (degree_le_of_natDegree_le h).trans_lt (mod_cast Nat.lt_succ_self k)

end Helpers

end ChabautyColeman

end
