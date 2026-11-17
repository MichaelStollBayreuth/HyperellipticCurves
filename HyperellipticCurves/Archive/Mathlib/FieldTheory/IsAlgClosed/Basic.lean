/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Beyond the sibling, for the proof only: `Polynomial.support_rootMultiplicity_subset` (the
-- mirror of `Mathlib.Algebra.Polynomial.Roots`).
import HyperellipticCurves.Mathlib.Algebra.Polynomial.Roots

/-!
# Root multiplicities over an algebraically closed field sum to the degree

## Main statements

* `ChabautyColeman.finsum_rootMultiplicity`: over an algebraically closed field the root
  multiplicities of a polynomial sum to its degree.

Its clients are the chart-form divisor-specialization statement
(`HyperellipticCurves.Archive.SpecializationGeneric`) and the exact canonical degree `2g-2`
(`HyperellipticCurves.Archive.CanonDegExact`). The main development needs only the inequality
`Polynomial.finsum_rootMultiplicity_le`, which holds over any field.

Auxiliary material for the Archive of the formalization of the Chabauty–Coleman bound for
hyperelliptic curves (the main theorems do not depend on it); an upstreaming candidate for
Mathlib.
-/

@[expose] public section

open Polynomial

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
