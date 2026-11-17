/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Monic

-- Beyond the sibling, for the proof of `Polynomial.Monic.eq_add_sum_coeff_sub` only: the tactic
-- `linear_combination`.
import Mathlib.Tactic.LinearCombination

/-!
# Monic polynomials: degrees under base change, lower-order parts, and small multiples

## Main statements

* `Polynomial.Monic.degree_map_lt_degree_map`: base change preserves a strict degree inequality
  below a monic polynomial.
* `Polynomial.Monic.eq_add_sum_coeff_sub`: two monic polynomials of the same degree `n` differ
  by their coefficients below `n`.
* `Polynomial.Monic.eq_zero_of_dvd_of_degree_lt`: over any commutative ring, a multiple of a
  monic polynomial of smaller degree is zero.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- Base change preserves a strict degree inequality below a monic polynomial: the larger
degree is unchanged, the smaller one can only drop. -/
theorem Monic.degree_map_lt_degree_map {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S]
    {p q : R[X]} (hq : q.Monic) (φ : R →+* S) (h : p.degree < q.degree) :
    (p.map φ).degree < (q.map φ).degree :=
  degree_map_le.trans_lt (h.trans_eq (hq.degree_map φ).symm)

variable {K : Type*} [Field K]

variable {S : Type*} [CommRing S] [Nontrivial S]

/-- Two monic polynomials of the same degree `n` differ by their lower-order coefficients:
`P = Q + ∑_{i<n} (P - Q)ᵢ Xⁱ`. -/
theorem Monic.eq_add_sum_coeff_sub {P Q : Polynomial S} {n : ℕ}
    (hP : P.Monic) (hQ : Q.Monic) (hPn : P.natDegree = n) (hQn : Q.natDegree = n) :
    P = Q + ∑ i : Fin n, C ((P - Q).coeff (i : ℕ)) * X ^ (i : ℕ) := by
  have hdP : P.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree hP.ne_zero, hPn]
  have hdQ : Q.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree hQ.ne_zero, hQn]
  have hdeg : (P - Q).degree < (n : WithBot ℕ) := by
    have h := degree_sub_lt_left (hdP.trans hdQ.symm) hP.ne_zero
      (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rwa [hdP] at h
  suffices h : P - Q = ∑ i : Fin n, C ((P - Q).coeff (i : ℕ)) * X ^ (i : ℕ) by
    linear_combination h
  by_cases hD : P - Q = 0
  · rw [hD]
    exact (Finset.sum_eq_zero fun i _ ↦ by simp).symm
  · have hlt : (P - Q).natDegree < n := (natDegree_lt_iff_degree_lt hD).mpr hdeg
    calc P - Q = ∑ i ∈ Finset.range n, monomial i ((P - Q).coeff i) :=
          as_sum_range' _ n hlt
      _ = ∑ i : Fin n, C ((P - Q).coeff (i : ℕ)) * X ^ (i : ℕ) := by
          rw [Finset.sum_range fun i ↦ monomial i ((P - Q).coeff i)]
          exact Finset.sum_congr rfl fun i _ ↦ (C_mul_X_pow_eq_monomial).symm

/-- Over any commutative ring, a multiple of a monic polynomial of smaller degree is
zero. -/
theorem Monic.eq_zero_of_dvd_of_degree_lt {R : Type*} [CommRing R] {p q : R[X]}
    (hp : p.Monic) (h₁ : p ∣ q) (h₂ : q.degree < p.degree) : q = 0 := by
  obtain ⟨c, rfl⟩ := h₁
  rcases eq_or_ne c 0 with rfl | hc
  · rw [mul_zero]
  refine absurd h₂ (not_lt.mpr ?_)
  have hd : (p * c).degree = p.degree + c.degree :=
    degree_mul' (by rw [hp.leadingCoeff, one_mul]; exact leadingCoeff_ne_zero.mpr hc)
  rw [hd]
  exact le_add_of_nonneg_right (zero_le_degree_iff.mpr hc)

end Polynomial

end
