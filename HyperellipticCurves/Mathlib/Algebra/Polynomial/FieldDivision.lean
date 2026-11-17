/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: `Squarefree`, which the statement of
-- `Squarefree.exists_mul_eq_sub_sq_and_isCoprime` needs.
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic

-- For the proofs only: `Polynomial.exists_isCoprime_eval_mul` and the tactic `linear_combination`.
import HyperellipticCurves.Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination

/-!
# Square factors, polynomials with enough distinct roots, and coprime values

## Main statements

* `Polynomial.X_sub_C_sq_dvd_iff`: `(X - C a) ^ 2 ∣ p` if and only if `p` and its derivative both
  vanish at `a`.
* `Polynomial.eq_C_leadingCoeff_mul_prod_X_sub_C_of_injective`: a polynomial of degree at most
  `card ι` with the distinct roots `α i` is `C (leadingCoeff f) * ∏ i, (X - α i)`, and
  `Polynomial.squarefree_of_injective`: such an `f ≠ 0` is squarefree.
* `Polynomial.exists_isCoprime_eval`: in a principal ideal domain, if no prime factor of `N ≠ 0`
  divides all values of `Q`, then some value of `Q` is coprime to `N`.
* `Squarefree.exists_mul_eq_sub_sq_and_isCoprime`: the moving lemma of [Sto17], Section 5, in a
  principal ideal domain in which `2` is a unit.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5

Auxiliary material for the formalization of the Chabauty–Coleman bound and of `2`-descent for
hyperelliptic curves; upstreaming candidates for Mathlib.
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

/-! ### Values prime to a given element -/

open Polynomial

-- If `f - b ^ 2 = a * c` with `f` squarefree and `2` a unit, then a non-unit `p` does not divide
-- all values of `c - 2 * b * t - a * t ^ 2`: if it divides those at `t = 0, 1, -1`, it divides
-- `a`, `b` and `c`, so `p * p` divides `f = b * b + a * c`.
private theorem Squarefree.exists_not_dvd_sub_mul_sub_mul_sq {R : Type*} [CommRing R]
    {f a b c p : R} (hf : Squarefree f) (h2 : IsUnit (2 : R)) (hp : ¬IsUnit p)
    (h : f - b ^ 2 = a * c) : ∃ t, ¬p ∣ c - 2 * b * t - a * t ^ 2 := by
  by_contra! H
  have hc : p ∣ c := (H 0).trans (dvd_of_eq (by ring))
  have hb : p ∣ b :=
    (h2.mul h2).dvd_mul_left.mp (((H (-1)).sub (H 1)).trans (dvd_of_eq (by ring)))
  have ha : p ∣ a :=
    h2.dvd_mul_left.mp ((((H 0).mul_left 2).sub ((H 1).add (H (-1)))).trans (dvd_of_eq (by ring)))
  exact hp (hf p (((mul_dvd_mul hb hb).add (mul_dvd_mul ha hc)).trans
    (dvd_of_eq (by linear_combination -h))))

section PID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- In a principal ideal domain, if no prime factor of `N ≠ 0` divides all values of `Q`, then
some value of `Q` is coprime to `N`: induction on the prime factors of `N`, with
`Polynomial.exists_isCoprime_eval_mul`. -/
theorem Polynomial.exists_isCoprime_eval {Q : R[X]} {N : R} (hN : N ≠ 0)
    (h : ∀ p, Prime p → p ∣ N → ∃ t, ¬p ∣ Q.eval t) : ∃ k, IsCoprime (Q.eval k) N := by
  induction N using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hN
  | h₂ x hx => exact ⟨0, isCoprime_one_right.of_isCoprime_of_dvd_right hx.dvd⟩
  | h₃ a p ha hp ih =>
    obtain ⟨k, hk⟩ := ih ha fun q hq hqa ↦ h q hq (hqa.mul_left p)
    by_cases hpa : p ∣ a
    · exact ⟨k, (hk.of_isCoprime_of_dvd_right hpa).mul_right hk⟩
    · obtain ⟨t, ht⟩ := h p hp (dvd_mul_right p a)
      exact exists_isCoprime_eval_mul (hp.coprime_iff_not_dvd.mpr hpa)
        (hp.coprime_iff_not_dvd.mpr ht).symm hk

/-- The **moving lemma** of [Sto17], Section 5, in a principal ideal domain where `2` is a unit:
for `a ∣ b ^ 2 - f` with `f` squarefree and any `N ≠ 0`, the cofactor of `a` in
`f - (b + k * a) ^ 2` is coprime to `N` for some `k`. It is the value at `k` of the quadratic
`c - 2 * b * t - a * t ^ 2`, where `f - b ^ 2 = a * c`; a prime dividing its values at
`t = 0, 1, -1` would divide `a`, `b` and `c`, so its square would divide `f`. Then `k` comes from
`Polynomial.exists_isCoprime_eval`. -/
theorem Squarefree.exists_mul_eq_sub_sq_and_isCoprime {f a b N : R} (hf : Squarefree f)
    (h2 : IsUnit (2 : R)) (h : a ∣ b ^ 2 - f) (hN : N ≠ 0) :
    ∃ k a'', a * a'' = f - (b + k * a) ^ 2 ∧ IsCoprime a'' N := by
  obtain ⟨c, hc⟩ := dvd_sub_comm.mp h
  obtain ⟨k, hk⟩ := exists_isCoprime_eval (Q := C c - C (2 * b) * X - C a * X ^ 2) hN
    fun p hp _ ↦ by simpa using hf.exists_not_dvd_sub_mul_sub_mul_sq h2 hp.not_isUnit hc
  exact ⟨k, _, by simp; linear_combination -hc, hk⟩

end PID

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]} {ι : Type*} [Fintype ι] {α : ι → K}

/-- A polynomial over a field with distinct roots `α i`, at least `natDegree f` many, is its
leading coefficient times `∏ i, (X - C (α i))`. -/
theorem eq_C_leadingCoeff_mul_prod_X_sub_C_of_injective (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) :
    f = C f.leadingCoeff * ∏ i, (X - C (α i)) := by
  refine eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (α i))
    (Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _)
      fun i _ ↦ dvd_iff_isRoot.mpr (hroot i)) ?_
  rwa [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]

/-- A nonzero polynomial over a field with distinct roots `α i`, at least `natDegree f` many, is
squarefree. -/
theorem squarefree_of_injective (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) : Squarefree f := by
  rw [eq_C_leadingCoeff_mul_prod_X_sub_C_of_injective hinj hroot hcard]
  refine (associated_unit_mul_left _ _ (isUnit_C.mpr (leadingCoeff_ne_zero.mpr hf).isUnit)
    ).squarefree_iff.mpr ?_
  exact Finset.squarefree_prod_of_pairwise_isCoprime
    (fun i _ j _ hij ↦ (pairwise_coprime_X_sub_C hinj hij).isRelPrime)
    fun i _ ↦ (irreducible_X_sub_C _).squarefree

end Polynomial

end
