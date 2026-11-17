/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision

-- Beyond the sibling, for the proof of `Polynomial.isCoprime_X_sub_C_of_isUnit_eval` only: the
-- tactic `linear_combination`.
import Mathlib.Tactic.LinearCombination

/-!
# The top-coefficient functional, and coprimality with linear factors

The *top-coefficient functional* `Polynomial.topCoeffMod u` of a monic polynomial `u` is the
coefficient of `X ^ (deg u - 1)` in `p %ₘ u`. Classically it is the trace form
`Tr(p / u')` — Euler's identity — but the coefficient description needs neither the trace nor
separability of `u`.

## Main definitions

* `Polynomial.topCoeffMod`: the top-coefficient functional.

## Main statements

* `Polynomial.topCoeffMod_congr`, `Polynomial.topCoeffMod_C_mul`, `Polynomial.topCoeffMod_map`:
  the functional only sees `p` modulo `u`, is `R`-linear, and commutes with base change.
* `Polynomial.topCoeffMod_eq_zero_of_natDegree_lt`: it vanishes below the top degree (the
  elementary form of `Tr(p / u') = 0` for `deg p ≤ deg u - 2`).
* `Polynomial.exists_topCoeffMod_ne_zero`: it separates residues modulo `u`.
* `Polynomial.topCoeffMod_mul_monic`: **the localization lemma** — passing from `u` to `u * w`
  and from `q` to `q * w`, for a monic `w`, does not change the functional; no coprimality is
  needed.
* `Polynomial.mul_modByMonic_mul`: `(q * w) %ₘ (u * w) = (q %ₘ u) * w` for monic `u`, `w`.
* `Polynomial.rootMultiplicity_zero_X_pow_mul`: the multiplicity of `0` as a root of `X ^ d * q`
  with `q(0) ≠ 0` is `d`.
* `Polynomial.Monic.dvd_of_C_mul_dvd`: a monic polynomial dividing `C a * W` with `a` regular
  divides `W`.
* `Polynomial.isCoprime_X_sub_C_of_isUnit_eval`, `Polynomial.isCoprime_X_sub_C_of_eval_ne_zero`:
  coprimality with `X - C x` from a unit (nonzero) value at `x`.
* `Polynomial.pair_dvd_of_eval`: a polynomial vanishing at two distinct points is divisible by
  the product of the two linear factors.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- The multiplicity of `0` as a root of `X ^ d · q`, with `q(0) ≠ 0`, is `d`. -/
theorem rootMultiplicity_zero_X_pow_mul {F : Type*} [Field F] (d : ℕ)
    {q : F[X]} (hq : q.coeff 0 ≠ 0) : ((X : F[X]) ^ d * q).rootMultiplicity 0 = d := by
  have hqne : q ≠ 0 := fun h ↦ hq (by rw [h, coeff_zero])
  have h0 : q.rootMultiplicity 0 = 0 :=
    rootMultiplicity_eq_zero fun hr ↦ hq (by rwa [IsRoot, ← coeff_zero_eq_eval_zero] at hr)
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero d X_ne_zero) hqne),
    rootMultiplicity_eq_natTrailingDegree', natTrailingDegree_X_pow, h0, add_zero]

section TopCoeff

variable {R : Type*} [CommRing R] {u w p q : R[X]}

/-- The **top-coefficient functional** of a monic polynomial: the coefficient of
`X^(deg u - 1)` in `p mod u`. Classically it is the trace form `Tr(p / u')` — Euler's
identity — but the coefficient description needs neither the trace nor separability of `u`. -/
noncomputable def topCoeffMod (u p : R[X]) : R := (p %ₘ u).coeff (u.natDegree - 1)

@[simp] theorem topCoeffMod_zero (u : R[X]) : topCoeffMod u 0 = 0 := by simp [topCoeffMod]

theorem topCoeffMod_add (p q : R[X]) :
    topCoeffMod u (p + q) = topCoeffMod u p + topCoeffMod u q := by
  simp [topCoeffMod, add_modByMonic]

@[simp] theorem topCoeffMod_neg (p : R[X]) : topCoeffMod u (-p) = -topCoeffMod u p := by
  simp [topCoeffMod, neg_modByMonic]

/-- The functional only sees `p` modulo `u`. -/
theorem topCoeffMod_congr (hu : u.Monic) (h : u ∣ p - q) :
    topCoeffMod u p = topCoeffMod u q := by
  rw [topCoeffMod, topCoeffMod, modByMonic_eq_of_dvd_sub hu h]

theorem topCoeffMod_sum {ι : Type*} (s : Finset ι) (p : ι → R[X]) :
    topCoeffMod u (∑ i ∈ s, p i) = ∑ i ∈ s, topCoeffMod u (p i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, topCoeffMod_add, ih]

/-- The functional is `R`-linear; only additivity and this are needed to expand it along a
chart decomposition of the modulus. -/
theorem topCoeffMod_C_mul (a : R) (p : R[X]) :
    topCoeffMod u (C a * p) = a * topCoeffMod u p := by
  rw [topCoeffMod, topCoeffMod, ← smul_eq_C_mul, smul_modByMonic, coeff_smul, smul_eq_mul]

/-- The functional commutes with base change, the modulus being monic. -/
theorem topCoeffMod_map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S) (hu : u.Monic)
    (p : R[X]) : topCoeffMod (u.map φ) (p.map φ) = φ (topCoeffMod u p) := by
  rw [topCoeffMod, topCoeffMod, ← Polynomial.map_modByMonic φ hu, coeff_map, hu.natDegree_map]

variable [Nontrivial R]

/-- Below the top degree the functional vanishes — the elementary form of Euler's identity
`Tr(p / u') = 0` for `deg p ≤ deg u - 2`. -/
theorem topCoeffMod_eq_zero_of_natDegree_lt (hu : u.Monic) (hp : p.natDegree + 1 < u.natDegree) :
    topCoeffMod u p = 0 := by
  have hlt : p.degree < u.degree := by
    refine degree_le_natDegree.trans_lt ?_
    rw [degree_eq_natDegree hu.ne_zero]
    exact_mod_cast Nat.lt_of_succ_lt hp
  rw [topCoeffMod, (modByMonic_eq_self_iff hu).mpr hlt]
  exact coeff_eq_zero_of_natDegree_lt (by lia)

/-- The functional separates residues: a nonzero residue modulo `u` is detected by `X^m` for
some `m < deg u`. Choose `m` so that `X^m·(p mod u)` has degree exactly `deg u - 1`; then no
reduction happens and the top coefficient is the leading coefficient of `p mod u`. -/
theorem exists_topCoeffMod_ne_zero (hu : u.Monic) (hp : p %ₘ u ≠ 0) :
    ∃ m < u.natDegree, topCoeffMod u (X ^ m * p) ≠ 0 := by
  have hlt : (p %ₘ u).natDegree < u.natDegree := by
    have h := degree_modByMonic_lt p hu
    rw [degree_eq_natDegree hp, degree_eq_natDegree hu.ne_zero] at h
    exact_mod_cast h
  set d := (p %ₘ u).natDegree with hd
  set m := u.natDegree - 1 - d
  have hsum : d + m = u.natDegree - 1 := by lia
  refine ⟨m, by lia, ?_⟩
  have hcongr : topCoeffMod u (X ^ m * p) = topCoeffMod u (X ^ m * (p %ₘ u)) := by
    refine topCoeffMod_congr hu ?_
    rw [← mul_sub]
    exact (dvd_sub_comm.mp (dvd_modByMonic_sub p u)).mul_left _
  have hdeg : (X ^ m * (p %ₘ u)).degree < u.degree := by
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    rw [degree_X_pow, degree_eq_natDegree hp, degree_eq_natDegree hu.ne_zero, ← hd]
    exact_mod_cast by lia
  rw [hcongr, topCoeffMod, (modByMonic_eq_self_iff hu).mpr hdeg, ← hsum, coeff_X_pow_mul]
  exact leadingCoeff_ne_zero.mpr hp

/-- Reduction modulo a monic product, after multiplying by one of the factors: the second
factor comes out of the reduction. -/
theorem mul_modByMonic_mul (hu : u.Monic) (hw : w.Monic) (q : R[X]) :
    (q * w) %ₘ (u * w) = (q %ₘ u) * w := by
  rcases eq_or_ne u 1 with rfl | hu1
  · rw [one_mul, modByMonic_one, zero_mul,
      (modByMonic_eq_zero_iff_dvd hw).mpr (dvd_mul_left w q)]
  have hr := natDegree_modByMonic_lt q hu hu1
  have hdeg : ((q %ₘ u) * w).degree < (u * w).degree := by
    refine (degree_mul_le _ _).trans_lt ?_
    rw [degree_eq_natDegree (hu.mul hw).ne_zero, hu.natDegree_mul hw,
      degree_eq_natDegree hw.ne_zero]
    have hqd : ((q %ₘ u).degree) ≤ ((u.natDegree - 1 : ℕ) : WithBot ℕ) :=
      degree_le_natDegree.trans (Nat.cast_le.mpr (by lia))
    calc (q %ₘ u).degree + (w.natDegree : WithBot ℕ)
        ≤ ((u.natDegree - 1 : ℕ) : WithBot ℕ) + (w.natDegree : WithBot ℕ) := by gcongr
      _ < ((u.natDegree + w.natDegree : ℕ) : WithBot ℕ) := by
          rw [← Nat.cast_add]
          exact_mod_cast by lia
  refine (div_modByMonic_unique (q /ₘ u) _ (hu.mul hw) ⟨?_, hdeg⟩).2
  conv_rhs => rw [← modByMonic_add_div q u]
  ring

private theorem natDegree_sub_X_pow_lt (hw : w.Monic) (hw0 : 0 < w.natDegree) :
    (w - X ^ w.natDegree).natDegree < w.natDegree := by
  rcases eq_or_ne (w - X ^ w.natDegree) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    exact hw0
  · have hdeg : w.degree = (X ^ w.natDegree : R[X]).degree := by
      rw [degree_X_pow, degree_eq_natDegree hw.ne_zero]
    have h := degree_sub_lt_left hdeg hw.ne_zero
      (by rw [hw.leadingCoeff, monic_X_pow _ |>.leadingCoeff])
    rw [degree_eq_natDegree h0, degree_eq_natDegree hw.ne_zero] at h
    exact_mod_cast h

/-- **The localization lemma**: multiplying by a monic `w` and passing from `u` to `u*w` does
not change the functional. No coprimality is needed — in particular `w = u` is allowed, which
is what the doubling case of Cantor composition requires. Both degenerate cases `u = 1` and
`w = 1` are included: there both sides are `0`. -/
theorem topCoeffMod_mul_monic (hu : u.Monic) (hw : w.Monic) (q : R[X]) :
    topCoeffMod (u * w) (q * w) = topCoeffMod u q := by
  rcases eq_or_ne u 1 with rfl | hu1
  · rw [one_mul, topCoeffMod, topCoeffMod, modByMonic_one,
      (modByMonic_eq_zero_iff_dvd hw).mpr (dvd_mul_left w q)]
    simp
  rcases Nat.eq_zero_or_pos w.natDegree with hw0 | hw0
  · rw [eq_one_of_monic_natDegree_zero hw hw0, mul_one, mul_one]
  have hu0 : 0 < u.natDegree :=
    Nat.pos_of_ne_zero fun h ↦ hu1 (eq_one_of_monic_natDegree_zero hu h)
  have hr := natDegree_modByMonic_lt q hu hu1
  rw [topCoeffMod, mul_modByMonic_mul hu hw, hu.natDegree_mul hw,
    show (q %ₘ u) * w = (q %ₘ u) * (w - X ^ w.natDegree) + (q %ₘ u) * X ^ w.natDegree by
      ring, coeff_add, coeff_mul_X_pow']
  -- only the leading term of `w` reaches the top coefficient
  have hlow : ((q %ₘ u) * (w - X ^ w.natDegree)).natDegree < u.natDegree + w.natDegree - 1 := by
    refine natDegree_mul_le.trans_lt ?_
    lia [natDegree_sub_X_pow_lt hw hw0]
  rw [coeff_eq_zero_of_natDegree_lt hlow, zero_add, ite_eq_left (by lia)]
  congr 1
  lia

end TopCoeff

/-- A monic polynomial dividing a regular constant multiple divides the polynomial itself. -/
theorem Monic.dvd_of_C_mul_dvd {R : Type*} [CommRing R] [IsDomain R] {U W : R[X]} {a : R}
    (hU : U.Monic) (ha : a ≠ 0) (h : U ∣ C a * W) : U ∣ W := by
  rw [← modByMonic_eq_zero_iff_dvd hU] at h ⊢
  rw [show (C a * W : R[X]) = a • W by rw [smul_eq_C_mul], smul_modByMonic] at h
  have h2 : ∀ i, a * (W %ₘ U).coeff i = 0 := fun i ↦ by
    have := congrArg (fun p ↦ Polynomial.coeff p i) h
    simpa [coeff_smul, smul_eq_mul] using this
  ext i
  rw [coeff_zero]
  exact (mul_eq_zero.mp (h2 i)).resolve_left ha

variable {K : Type*} [Field K]

/-- Coprimality with a linear factor from an invertible value. Over a ring the value need not
be a unit on the nose — this is the form that applies after localizing to make it one. -/
theorem isCoprime_X_sub_C_of_isUnit_eval {R : Type*} [CommRing R] {P : R[X]} {x : R}
    (h : IsUnit (P.eval x)) : IsCoprime P (X - C x) := by
  obtain ⟨Q, hQ⟩ := X_sub_C_dvd_sub_C_eval (a := x) (p := P)
  obtain ⟨c, hc⟩ := h.exists_left_inv
  have hc' : (C c : R[X]) * C (P.eval x) = 1 := by rw [← C_mul, hc, map_one]
  exact ⟨C c, -(C c * Q), by linear_combination (C c : R[X]) * hQ + hc'⟩

/-- Coprimality with a linear factor from a nonzero evaluation. -/
theorem isCoprime_X_sub_C_of_eval_ne_zero {P : K[X]} {x : K} (h : P.eval x ≠ 0) :
    IsCoprime P (X - C x) := isCoprime_X_sub_C_of_isUnit_eval h.isUnit

/-- A polynomial vanishing at two distinct points is divisible by the pair. -/
theorem pair_dvd_of_eval {p : K[X]} {a c : K} (hne : a ≠ c) (h₁ : p.eval a = 0)
    (h₂ : p.eval c = 0) : (X - C a) * (X - C c) ∣ p :=
  IsCoprime.mul_dvd
    (isCoprime_X_sub_C_of_eval_ne_zero (by simpa using sub_ne_zero.mpr (Ne.symm hne)))
    (dvd_iff_isRoot.mpr h₁) (dvd_iff_isRoot.mpr h₂)

end Polynomial

end
