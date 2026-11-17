/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Finiteness of `n`-th roots, and sums of root multiplicities

## Main statements

* `Polynomial.finite_setOf_pow_eq`: an element of a domain has finitely many `n`-th roots.
* `Polynomial.support_rootMultiplicity_subset`: the support of `x ↦ rootMultiplicity x h` lies in
  the finite set of roots of `h`.
* `Polynomial.finsum_rootMultiplicity_le`: over any field, the root multiplicities sum to at
  most the degree.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- **A ring element in a domain has finitely many `n`-th roots** — they are the roots of
`X ^ n - a`, listed by `Polynomial.nthRoots`. -/
theorem finite_setOf_pow_eq {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} (hn : 0 < n)
    (a : R) :
    {y : R | y ^ n = a}.Finite :=
  (nthRoots n a).finite_toSet.subset fun _ hy ↦ by
    simpa only [Multiset.mem_coe, mem_nthRoots hn] using hy

/-- The support of `x₀ ↦ rootMultiplicity x₀ h` is contained in the (finite) set of roots of `h`
(needs `classical` in scope for `DecidableEq`). -/
theorem support_rootMultiplicity_subset {κ : Type*} [Field κ] [DecidableEq κ] (h : κ[X]) :
    Function.support (fun x₀ : κ ↦ rootMultiplicity x₀ h) ⊆ ↑h.roots.toFinset := by
  intro x hx
  simp only [Function.mem_support] at hx
  rw [Finset.mem_coe, Multiset.mem_toFinset]
  exact Multiset.count_pos.mp (by rw [count_roots]; exact Nat.pos_of_ne_zero hx)

/-- The sum of root multiplicities over any field is at most the degree. -/
theorem finsum_rootMultiplicity_le {κ : Type*} [Field κ] (h : κ[X]) :
    ∑ᶠ x₀ : κ, rootMultiplicity x₀ h ≤ h.natDegree := by
  classical
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  rw [finsum_eq_finsetSum_of_support_subset _ (support_rootMultiplicity_subset h)]
  calc ∑ x ∈ h.roots.toFinset, rootMultiplicity x h
      = ∑ x ∈ h.roots.toFinset, h.roots.count x :=
        Finset.sum_congr rfl fun x _ ↦ (count_roots h).symm
    _ = Multiset.card h.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ h.natDegree := card_roots' h

end Polynomial

end
