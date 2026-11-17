/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Square factors detected by two evaluations

## Main statements

* `Polynomial.X_sub_C_sq_dvd_iff`: `(X - C a) ^ 2 ∣ p` if and only if `p` and its derivative both
  vanish at `a`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- **A square factor `(X - a)²` is detected by two evaluations**: the polynomial and its
derivative both vanish at `a`. -/
theorem X_sub_C_sq_dvd_iff {R : Type*} [CommRing R] {p : R[X]} {a : R} :
    (X - C a) ^ 2 ∣ p ↔ p.eval a = 0 ∧ p.derivative.eval a = 0 := by
  refine ⟨fun ⟨q, hq⟩ ↦ ⟨by simp [hq], by simp [hq, derivative_mul, derivative_pow]⟩,
    fun ⟨h0, h1⟩ ↦ ?_⟩
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr h0
  have hqa : q.eval a = 0 := by
    simpa [derivative_mul, h1] using (congrArg (fun r ↦ (derivative r).eval a) hq).symm
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqa
  exact ⟨r, by rw [hq, hr]; ring⟩

end Polynomial

end
