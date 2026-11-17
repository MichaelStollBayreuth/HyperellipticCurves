/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Finitely many polynomials of bounded degree with coefficients in a finite set

## Main statements

* `Polynomial.finite_setOf_natDegree_le_of_coeff_mem`: there are only finitely many polynomials
  of bounded degree all of whose coefficients lie in a given finite set.

Its client is the finite-index theorem for `J¹` (`HyperellipticCurves.Archive.J1FiniteIndex`).

Auxiliary material for the Archive of the formalization of the Chabauty–Coleman bound for
hyperelliptic curves (the main theorems do not depend on it); an upstreaming candidate for
Mathlib.
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

end
