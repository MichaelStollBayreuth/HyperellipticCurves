/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.Algebra.Polynomial.Reverse`: algebras, for the statement of
-- `Polynomial.sq_inv_mul_inv_pow_eq_eval₂_inv`.
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Reverse

-- For the proof of `Polynomial.sq_inv_mul_inv_pow_eq_eval₂_inv` only: the tactic
-- `linear_combination`.
import Mathlib.Tactic.LinearCombination

/-!
# Reflecting within a longer window, and reflected points on `y ^ 2 = g(x)`

## Main statements

* `Polynomial.reflect_succ`: `reflect (M + 1) p = X * reflect M p` for `deg p ≤ M`.
* `Polynomial.sq_inv_mul_inv_pow_eq_eval₂_inv`: if `A = Z ^ 2 * g.reverse(A)` for a polynomial
  `g` of degree `2 * n + 1` and nonzero `A`, `Z` in an extension field, then
  `(Z⁻¹ * A⁻¹ ^ n) ^ 2 = g(A⁻¹)`: the reflected point lies on the curve `y ^ 2 = g(x)`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- `reflect (M+1) p = X · reflect M p` when `deg p ≤ M` (reversing within a longer window shifts
the reflected polynomial up by one). -/
theorem reflect_succ {O : Type*} [CommRing O] {p : O[X]} {M : ℕ} (hp : p.natDegree ≤ M) :
    reflect (M + 1) p = Polynomial.X * reflect M p := by
  ext i
  rw [coeff_reflect]
  rcases i with _ | n
  · rw [coeff_X_mul_zero, revAt_le (Nat.zero_le _), coeff_eq_zero_of_natDegree_lt (by lia)]
  · rw [coeff_X_mul, coeff_reflect]
    rcases le_or_gt n M with hn | hn
    · rw [revAt_le (by lia), revAt_le hn]; congr 1; lia
    · rw [revAt_eq_self_of_lt (by lia), revAt_eq_self_of_lt hn,
        coeff_eq_zero_of_natDegree_lt (by lia), coeff_eq_zero_of_natDegree_lt (by lia)]

/-- **The reflected point lies on the curve**: if `A = Z² · g^rev(A)` for a polynomial `g` of
degree `2n + 1` and nonzero `A`, `Z` in an extension field, then `(Z⁻¹ A⁻ⁿ)² = g(A⁻¹)`. -/
theorem sq_inv_mul_inv_pow_eq_eval₂_inv {K L : Type*} [Field K] [Field L] [Algebra K L]
    {g : K[X]} {n : ℕ} (hdeg : g.natDegree = 2 * n + 1) {A Z : L} (hA : A ≠ 0) (hZ : Z ≠ 0)
    (hAeq : A = Z ^ 2 * eval₂ (algebraMap K L) A g.reverse) :
    (Z⁻¹ * A⁻¹ ^ n) ^ 2 = eval₂ (algebraMap K L) A⁻¹ g := by
  let : Invertible A := invertibleOfNonzero hA
  have hrev : g.reverse = reflect (2 * n + 1) g := by rw [Polynomial.reverse, hdeg]
  have hrefl := eval₂_reflect_mul_pow (algebraMap K L) A (2 * n + 1) (reflect (2 * n + 1) g)
    (natDegree_reflect_le.trans (max_le le_rfl hdeg.le))
  rw [reflect_reflect, invOf_eq_inv, ← hrev] at hrefl
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (2 * n + 1) hA) (pow_ne_zero 2 hZ)) ?_
  calc (Z⁻¹ * A⁻¹ ^ n) ^ 2 * (A ^ (2 * n + 1) * Z ^ 2)
      = (A⁻¹ * A) ^ (2 * n) * (Z⁻¹ * Z) ^ 2 * A := by ring
    _ = A := by
        rw [inv_mul_cancel₀ hA, inv_mul_cancel₀ hZ, one_pow, one_pow, one_mul, one_mul]
    _ = eval₂ (algebraMap K L) A⁻¹ g * (A ^ (2 * n + 1) * Z ^ 2) := by
        rw [← mul_assoc, hrefl]
        linear_combination hAeq

end Polynomial

end
