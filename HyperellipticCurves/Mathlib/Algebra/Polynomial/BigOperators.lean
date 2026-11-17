/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The degree of a product of powers of linear factors

## Main statements

* `Polynomial.natDegree_prod_X_sub_C_pow`: the degree of `∏ i ∈ s, (X - C (x i)) ^ k i` is
  `∑ i ∈ s, k i`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- The degree of a product of powers of monic linear factors is the total multiplicity.
(The exponent-free case is closed by `simp`.) -/
theorem natDegree_prod_X_sub_C_pow {R : Type*} [CommRing R] [Nontrivial R] {ι : Type*}
    (s : Finset ι) (x : ι → R) (k : ι → ℕ) :
    (∏ i ∈ s, (X - C (x i)) ^ k i).natDegree = ∑ i ∈ s, k i := by
  rw [natDegree_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C (x i)).pow (k i)]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [(monic_X_sub_C (x i)).natDegree_pow, natDegree_X_sub_C, mul_one]

end Polynomial

end
