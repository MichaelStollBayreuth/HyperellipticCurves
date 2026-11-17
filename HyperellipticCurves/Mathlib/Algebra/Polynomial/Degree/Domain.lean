/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Degrees and leading coefficients of `v ^ 2 - f` and `p ^ 2 - f * q ^ 2` for `f` of odd degree

## Main statements

* `Polynomial.natDegree_sq_sub_of_odd`: for `f` of odd degree,
  `deg (v ^ 2 - f) = max (2 * deg v) (deg f)`, the two arguments of the maximum never coinciding.
* `Polynomial.sq_mul_ne_sq_of_odd_natDegree`: a polynomial of odd degree is not a quotient of
  squares: `A ^ 2 * f ≠ B ^ 2` for `B ≠ 0`.
* `Polynomial.eq_zero_of_mul_sq_eq_mul_sq`, `Polynomial.ne_zero_of_dvd_sq_sub`: parity of degrees
  of `p * u ^ 2` and of squares.
* `Polynomial.isSquare_neg_leadingCoeff_pow_mul_leadingCoeff_sq_sub_mul_sq`: for `f` of odd
  degree, `(-f.leadingCoeff) ^ N.natDegree * N.leadingCoeff` is a square, `N = p ^ 2 - f * q ^ 2`.

Auxiliary material for the formalization of the Chabauty–Coleman bound and of `2`-descent for
hyperelliptic curves; upstreaming candidates for Mathlib.
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

open Polynomial

/-- If `p * q` has odd degree, the two sides of `p * u ^ 2 = q * v ^ 2` have degrees of
different parity unless `u = 0`. -/
theorem Polynomial.eq_zero_of_mul_sq_eq_mul_sq {R : Type*} [Semiring R] [NoZeroDivisors R]
    {p q u v : R[X]} (h : Odd (p * q).natDegree)
    (huv : p * u ^ 2 = q * v ^ 2) : u = 0 := by
  by_contra hu
  obtain ⟨hp, hq⟩ := mul_ne_zero_iff.mp (fun h0 ↦ by simp [h0] at h : p * q ≠ 0)
  have hv : v ^ 2 ≠ 0 := right_ne_zero_of_mul (huv ▸ mul_ne_zero hp (pow_ne_zero 2 hu))
  have := congr(natDegree $huv)
  rw [natDegree_mul hp (pow_ne_zero 2 hu), natDegree_mul hq hv, natDegree_pow, natDegree_pow]
    at this
  rw [natDegree_mul hp hq] at h
  obtain ⟨k, hk⟩ := h
  lia

/-- A polynomial of odd degree is not a square, so `0` does not divide `b ^ 2 - f`. -/
theorem Polynomial.ne_zero_of_dvd_sq_sub {R : Type*} [Ring R] [NoZeroDivisors R] {f a b : R[X]}
    (hf : Odd f.natDegree) (h : a ∣ b ^ 2 - f) : a ≠ 0 := by
  rintro rfl
  rw [zero_dvd_iff, sub_eq_zero] at h
  simp [← h, natDegree_pow, Nat.odd_iff] at hf

/-- For `f` of odd degree, the leading term of `p ^ 2 - f * q ^ 2` is that of `p ^ 2`, in even
degree, or that of `-f * q ^ 2`, in odd degree; so its leading coefficient is a square or
`-f.leadingCoeff` times a square, according to the parity of its degree. -/
theorem Polynomial.isSquare_neg_leadingCoeff_pow_mul_leadingCoeff_sq_sub_mul_sq {R : Type*}
    [CommRing R] [NoZeroDivisors R] {f : R[X]} (hf : Odd f.natDegree) (p q : R[X]) :
    IsSquare ((-f.leadingCoeff) ^ (p ^ 2 - f * q ^ 2).natDegree *
      (p ^ 2 - f * q ^ 2).leadingCoeff) := by
  rcases eq_or_ne q 0 with rfl | hq
  · rw [zero_pow two_ne_zero, mul_zero, sub_zero, natDegree_pow, leadingCoeff_pow]
    exact ⟨(-f.leadingCoeff) ^ p.natDegree * p.leadingCoeff, by ring⟩
  have hd : (f * q ^ 2).natDegree = f.natDegree + 2 * q.natDegree := by
    rw [natDegree_mul (ne_zero_of_natDegree_gt hf.pos) (pow_ne_zero 2 hq), natDegree_pow]
  obtain ⟨k, hk⟩ := hf
  rcases lt_or_gt_of_ne (show (p ^ 2).natDegree ≠ (f * q ^ 2).natDegree by
    rw [natDegree_pow, hd]; lia) with hlt | hlt
  · rw [natDegree_sub_eq_right_of_natDegree_lt hlt,
      leadingCoeff_sub_of_degree_lt' (degree_lt_degree hlt), hd, leadingCoeff_mul,
      leadingCoeff_pow, hk]
    exact ⟨(-f.leadingCoeff) ^ (k + 1 + q.natDegree) * q.leadingCoeff, by ring⟩
  · rw [natDegree_sub_eq_left_of_natDegree_lt hlt,
      leadingCoeff_sub_of_degree_lt (degree_lt_degree hlt), natDegree_pow, leadingCoeff_pow]
    exact ⟨(-f.leadingCoeff) ^ p.natDegree * p.leadingCoeff, by ring⟩

end
