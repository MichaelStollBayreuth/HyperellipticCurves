/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Rational functions of odd degree are not squares

## Main statements

* `RatFunc.not_isSquare_of_odd_intDegree`: a rational function of odd degree is not a square.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

open Polynomial

namespace RatFunc

variable {K : Type*} [Field K]

/-- A rational function of odd degree is not a square. -/
theorem not_isSquare_of_odd_intDegree {x : RatFunc K} (h : Odd x.intDegree) :
    ¬IsSquare x := by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with rfl | hr
  · simp at h
  · rw [intDegree_mul hr hr] at h
    obtain ⟨k, hk⟩ := h
    lia

end RatFunc

end
