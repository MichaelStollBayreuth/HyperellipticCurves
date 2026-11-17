/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff

-- Beyond the sibling, for the proof only: `Polynomial.coeff_sum_C_mul_X_pow` (the mirror of
-- `Mathlib.Algebra.Polynomial.Coeff`).
import HyperellipticCurves.Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficients of a displaced polynomial after base change

## Main statements

* `Polynomial.coeff_map_add_sum_C_mul_X_pow`: the `i`-th coefficient of
  `(p + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).map φ` is that of `p.map φ` plus `φ (c i)`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

section Coeffs

/-- The `i`-th coefficient of a polynomial displaced by coordinates `c`, after base change:
the displacement contributes exactly `φ (c i)`. -/
theorem coeff_map_add_sum_C_mul_X_pow {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (p : R[X]) (c : Fin n → R) (i : Fin n) :
    ((p + ∑ j : Fin n, C (c j) * X ^ (j : ℕ)).map φ).coeff (i : ℕ)
      = (p.map φ).coeff (i : ℕ) + φ (c i) := by
  rw [Polynomial.map_add, coeff_add, Polynomial.map_sum,
    Finset.sum_congr rfl fun j _ ↦ (by rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X] :
      ((C (c j) * X ^ (j : ℕ)).map φ) = C (φ (c j)) * X ^ (j : ℕ)),
    coeff_sum_C_mul_X_pow]

end Coeffs

end Polynomial

end
