/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.ForMathlib.Polynomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Two polynomial facts used only within the Archive

* `Polynomial.finite_setOf_natDegree_le_of_coeff_mem`: there are only finitely many
  polynomials of bounded degree with all coefficients in a given finite set. Its client is
  the finite-index theorem for `J¹` (`HyperellipticCurves.Archive.J1FiniteIndex`).
* `ChabautyColeman.finsum_rootMultiplicity`: over an algebraically closed field the root
  multiplicities of a polynomial sum to its degree. Its clients are the chart-form
  divisor-specialization statement (`HyperellipticCurves.Archive.SpecializationGeneric`) and
  the exact canonical degree `2g-2` (`HyperellipticCurves.Archive.CanonDegExact`). The main
  development needs only the inequality `ChabautyColeman.finsum_rootMultiplicity_le`, which
  holds over any field.
-/

@[expose] public section

open Polynomial

/-- There are only finitely many polynomials of bounded degree all of whose coefficients
lie in a given finite set. -/
theorem Polynomial.finite_setOf_natDegree_le_of_coeff_mem {R : Type*} [Semiring R]
    {E : Set R} (hE : E.Finite) (n : ℕ) :
    {p : R[X] | p.natDegree ≤ n ∧ ∀ i, p.coeff i ∈ E}.Finite := by
  refine Set.Finite.of_finite_image (f := fun p (i : Fin (n + 1)) ↦ p.coeff i)
    ((Set.Finite.pi fun _ ↦ hE).subset ?_) fun p hp q hq h ↦ ?_
  · rintro - ⟨p, hp, rfl⟩
    exact fun i _ ↦ hp.2 i
  · ext i
    rcases le_or_gt i n with hi | hi
    · exact congrFun h ⟨i, by lia⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt hi),
        coeff_eq_zero_of_natDegree_lt (hq.1.trans_lt hi)]

namespace ChabautyColeman

/-- The sum of root multiplicities over an algebraically closed field is the degree. -/
theorem finsum_rootMultiplicity {κ : Type*} [Field κ] [IsAlgClosed κ] (h : κ[X]) :
    ∑ᶠ x₀ : κ, rootMultiplicity x₀ h = h.natDegree := by
  classical
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  rw [finsum_eq_finsetSum_of_support_subset _ (support_rootMultiplicity_subset h),
    ← IsAlgClosed.card_roots_eq_natDegree,
    ← Multiset.toFinset_sum_count_eq]
  exact Finset.sum_congr rfl fun x _ ↦ (count_roots h).symm

end ChabautyColeman

end
