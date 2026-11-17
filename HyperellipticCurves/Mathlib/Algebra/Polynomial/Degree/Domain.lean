/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Degrees of `v ^ 2 - f` for `f` of odd degree

## Main statements

* `Polynomial.natDegree_sq_sub_of_odd`: for `f` of odd degree,
  `deg (v ^ 2 - f) = max (2 * deg v) (deg f)`, the two arguments of the maximum never coinciding.
* `Polynomial.sq_mul_ne_sq_of_odd_natDegree`: a polynomial of odd degree is not a quotient of
  squares: `A ^ 2 * f ≠ B ^ 2` for `B ≠ 0`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

section SqSub

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}

/-- The degree of the curve relation of a Mumford datum on `y² = f`:
`deg(v² - f) = max (2 deg v) (deg f)`, the two arguments of the maximum never coinciding
because `deg f` is odd. -/
theorem natDegree_sq_sub_of_odd (hf : Odd f.natDegree) (v : R[X]) :
    (v ^ 2 - f).natDegree = max (2 * v.natDegree) f.natDegree := by
  obtain ⟨g, hg⟩ := hf
  have hsq : (v ^ 2).natDegree = 2 * v.natDegree := natDegree_pow v 2
  rcases lt_trichotomy (2 * v.natDegree) f.natDegree with h | h | h
  · rw [natDegree_sub_eq_right_of_natDegree_lt (by lia)]
    lia
  · lia
  · rw [natDegree_sub_eq_left_of_natDegree_lt (by lia), hsq]
    lia

/-- A polynomial of odd degree is not a square times a square: the two sides of
`A² f = B²` have degrees of opposite parity. -/
theorem sq_mul_ne_sq_of_odd_natDegree (hf0 : f ≠ 0) (hf : Odd f.natDegree) {A B : R[X]}
    (hB : B ≠ 0) : A ^ 2 * f ≠ B ^ 2 := fun h ↦ by
  have hA : A ≠ 0 := fun h0 ↦ hB (by simpa [h0, pow_eq_zero_iff] using h.symm)
  have hdeg := congrArg natDegree h
  rw [natDegree_mul (pow_ne_zero 2 hA) hf0, natDegree_pow, natDegree_pow] at hdeg
  obtain ⟨k, hk⟩ := hf
  lia

end SqSub

end Polynomial

end
