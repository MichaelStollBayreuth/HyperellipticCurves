/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficients in the monomial basis indexed by `Fin n`

## Main statements

* `Polynomial.coeff_sum_C_mul_X_pow`: the coefficients of `∑ j : Fin n, C (c j) * X ^ (j : ℕ)`
  are the `c j`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

section Coeffs

/-- The coefficients of a polynomial written in the monomial basis indexed by `Fin n` are
the coefficients it is written with. -/
theorem coeff_sum_C_mul_X_pow {R : Type*} [Semiring R] {n : ℕ} (c : Fin n → R) (i : Fin n) :
    (∑ j : Fin n, C (c j) * X ^ (j : ℕ)).coeff (i : ℕ) = c i := by
  rw [finsetSum_coeff, Finset.sum_eq_single i
    (fun j _ hj ↦ by
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right fun h ↦ hj (Fin.val_injective h.symm), mul_zero])
    fun h ↦ absurd (Finset.mem_univ i) h]
  simp

end Coeffs

end Polynomial

end
