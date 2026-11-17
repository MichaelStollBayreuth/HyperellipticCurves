/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Irreducibility of monic quadratic polynomials

## Main statements

* `Polynomial.irreducible_X_sq_add_C_mul_X_add_C_of_not_isSquare`: a monic quadratic polynomial
  whose discriminant is not a square is irreducible.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K] {b c : K}

/-- A monic quadratic polynomial whose discriminant is not a square is irreducible: a root `x`
would give `b ^ 2 - 4 c = (2 x + b) ^ 2`. -/
theorem irreducible_X_sq_add_C_mul_X_add_C_of_not_isSquare (h : ¬ IsSquare (b ^ 2 - 4 * c)) :
    Irreducible (X ^ 2 + C b * X + C c) := by
  have hd : (X ^ 2 + C b * X + C c).natDegree = 2 := by compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hd]) fun x hx ↦
    h ⟨2 * x + b, ?_⟩
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hx
  linear_combination -4 * hx

end Polynomial
