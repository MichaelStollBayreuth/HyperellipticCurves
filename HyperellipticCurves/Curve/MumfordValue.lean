/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Polynomial.Content

import HyperellipticCurves.Mathlib.Algebra.GCDMonoid.Basic
import HyperellipticCurves.Mathlib.Algebra.Polynomial.Degree.Domain
import HyperellipticCurves.Mathlib.Algebra.Squarefree.Basic
import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot
import HyperellipticCurves.Mathlib.RingTheory.Bezout
import HyperellipticCurves.Mathlib.RingTheory.Norm.AdjoinRoot
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.EuclideanDomain

/-!
# The value of a Mumford polynomial

Let `K` be a field and `f : K[X]` squarefree, and let `L = AdjoinRoot f` with `θ` the image of `X`
and `c` the leading coefficient of `f`. For a polynomial `a`, with the monic `d = gcd a f` and
`a = d * a₁`, `f = d * f₁`, Section 5 of [Sto17] attaches to the Mumford pair `(a, b)` the class
of `m(a) = (-c) ^ deg a * lc(a)⁻¹ * (a(θ) - a₁(θ) * f₁(θ))` in `L^× / (L^×)^2`; this is the
`x - T` map of 2-descent. This file defines `m(a)` and proves that it is a unit for every Mumford
pair, multiplicative on polynomials prime to `f`, and a square on norms prime to `f`.

## Main definitions

* `ChabautyColeman.mumfordValue`: the value `m(a)` in `AdjoinRoot f`.

## Main statements

* `ChabautyColeman.mumfordValue_eq_of_mul_eq`: the value for any factorizations `a = d * a₁`,
  `f = d * f₁` with `d` monic and `a₁` prime to `f₁`;
  `ChabautyColeman.mumfordValue_of_isCoprime` is the case `d = 1`.
* `ChabautyColeman.isUnit_mumfordValue`: for `a ∣ b ^ 2 - f`, `m(a)` is a unit.
* `ChabautyColeman.mumfordValue_mul`: `m(a * a') = m(a) * m(a')` for `a` and `a'` prime to `f`.
* `ChabautyColeman.mumfordValue_C_mul`, `ChabautyColeman.mumfordValue_eq_of_associated`: `m(a)`
  does not change under constant factors.
* `ChabautyColeman.isSquare_mumfordValue_sq_sub_mul_sq`: for `f` of odd degree, the value of a
  norm `p ^ 2 - f * q ^ 2` prime to `f` is a square.
* `ChabautyColeman.map_mumfordValue`: `m(a)` commutes with homomorphisms of fields.
* `ChabautyColeman.isSquare_mumfordValue_mul_of_mul_eq_sub_sq`: for `a * a'' = f - v ^ 2` with
  `a''` prime to `f`, `m(a) * m(a'')` is a square.
* `ChabautyColeman.isSquare_norm_mumfordValue`: the norm of `m(a)` is a square.

## Implementation notes

The gcd of `K[X]` needs `DecidableEq K`; `ChabautyColeman.mumfordValue` takes it classically, and no
statement mentions the gcd: `ChabautyColeman.mumfordValue_eq_of_mul_eq` is the form later proofs
rewrite with.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K] (f : K[X])

open Classical in
/-- The value `m(a)` in `AdjoinRoot f` of a polynomial `a`, as in Section 5 of [Sto17]: with the
monic `d = gcd a f` and `a = d * a₁`, `f = d * f₁`, it is the image of
`(-c) ^ deg a * lc(a)⁻¹ * (a - a₁ * f₁)`, where `c` is the leading coefficient of `f`. For `a`
prime to `f` it is the image of `(-c) ^ deg a * lc(a)⁻¹ * a`
(`ChabautyColeman.mumfordValue_of_isCoprime`); for `a ∣ b ^ 2 - f` it is a unit
(`ChabautyColeman.isUnit_mumfordValue`). Its value at `a = 0` is `0`.

The gcd on `K[X]` needs decidable equality on `K`; it is taken classically, so that no
`DecidableEq K` reaches the API, as the normalized gcd does not depend on the instance. -/
noncomputable def mumfordValue (a : K[X]) : AdjoinRoot f :=
  AdjoinRoot.mk f (C ((-f.leadingCoeff) ^ a.natDegree * a.leadingCoeff⁻¹) *
    (a - a / gcd a f * (f / gcd a f)))

@[simp]
theorem mumfordValue_zero : mumfordValue f 0 = 0 := by
  simp [mumfordValue]

/-- `ChabautyColeman.mumfordValue` for any factorizations `a = d * a₁` and `f = d * f₁` with `d`
monic and `a₁` prime to `f₁`, which make `d` the gcd of `a` and `f`; the statement needs no
`DecidableEq K`. -/
theorem mumfordValue_eq_of_mul_eq {a d a₁ f₁ : K[X]} (hd : d.Monic) (ha : d * a₁ = a)
    (hf : d * f₁ = f) (h : IsCoprime a₁ f₁) :
    mumfordValue f a = AdjoinRoot.mk f
      (C ((-f.leadingCoeff) ^ a.natDegree * a.leadingCoeff⁻¹) * (a - a₁ * f₁)) := by
  classical
  have hg : gcd a f = d := by
    rw [← ha, ← hf, gcd_mul_left, gcd_eq_one_iff_isRelPrime.mpr h.isRelPrime, mul_one,
      hd.normalize_eq_self]
  rw [mumfordValue, hg, ← ha, ← hf, mul_div_cancel_left₀ _ hd.ne_zero,
    mul_div_cancel_left₀ _ hd.ne_zero]

theorem mumfordValue_of_isCoprime {a : K[X]} (ha : IsCoprime a f) :
    mumfordValue f a =
      AdjoinRoot.mk f (C ((-f.leadingCoeff) ^ a.natDegree * a.leadingCoeff⁻¹) * a) := by
  simp [mumfordValue_eq_of_mul_eq f monic_one (one_mul a) (one_mul f) ha]

/-- At `a = 0` the hypothesis forces `f = b ^ 2`, so `f` is a unit and `AdjoinRoot f` is the zero
ring; otherwise the constant factor is a unit and
`Squarefree.isCoprime_sub_mul_of_dvd_sq_sub` applies. -/
theorem isUnit_mumfordValue (hsf : Squarefree f) {a b : K[X]} (h : a ∣ b ^ 2 - f) :
    IsUnit (mumfordValue f a) := by
  obtain ⟨d, a₁, f₁, hd, had, hfd, hc⟩ := exists_monic_mul_eq_and_isCoprime (p := a) hsf.ne_zero
  have h' := hsf.isCoprime_sub_mul_of_dvd_sq_sub h had hfd hc
  rw [mumfordValue_eq_of_mul_eq f hd had hfd hc, AdjoinRoot.isUnit_mk_iff]
  rcases eq_or_ne a 0 with rfl | ha
  · simpa [(mul_eq_zero.mp had).resolve_left hd.ne_zero] using h'
  · rwa [isCoprime_mul_unit_left_left (isUnit_C.mpr (by simp [ha, hsf.ne_zero]))]

theorem mumfordValue_mul {a a' : K[X]} (ha : IsCoprime a f) (ha' : IsCoprime a' f) :
    mumfordValue f (a * a') = mumfordValue f a * mumfordValue f a' := by
  rcases eq_or_ne a 0 with rfl | h0
  · simp
  rcases eq_or_ne a' 0 with rfl | h0'
  · simp
  rw [mumfordValue_of_isCoprime f ha, mumfordValue_of_isCoprime f ha',
    mumfordValue_of_isCoprime f (ha.mul_left ha'), natDegree_mul h0 h0', leadingCoeff_mul]
  simp [pow_add]
  ring

/-- The factor `a.leadingCoeff⁻¹` in `ChabautyColeman.mumfordValue` makes the value invariant
under nonzero constant factors, as the class is (`ChabautyColeman.mumfordClass_C_mul`). -/
theorem mumfordValue_C_mul {lam : K} (hlam : lam ≠ 0) (a : K[X]) :
    mumfordValue f (C lam * a) = mumfordValue f a := by
  classical
  have hg := (associated_unit_mul_left a _ (isUnit_C.mpr hlam.isUnit)).gcd_eq_left f
  rw [mumfordValue, mumfordValue, hg, EuclideanDomain.mul_div_assoc _ (gcd_dvd_left a f),
    natDegree_C_mul hlam, leadingCoeff_mul, leadingCoeff_C, mul_assoc, ← mul_sub, ← mul_assoc,
    ← C_mul]
  congr 3
  field

theorem mumfordValue_eq_of_associated {a a' : K[X]} (h : Associated a a') :
    mumfordValue f a = mumfordValue f a' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨r, hr, hu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rw [← hu, mul_comm, mumfordValue_C_mul f hr.ne_zero]

/-- For `N = p ^ 2 - f * q ^ 2` prime to `f`, the value of `N` is the image of `C s * p ^ 2` in
`AdjoinRoot f`, with the constant `s = (-f.leadingCoeff) ^ N.natDegree * N.leadingCoeff⁻¹`, a
square in `K` by `Polynomial.isSquare_neg_leadingCoeff_pow_mul_leadingCoeff_sq_sub_mul_sq`. -/
theorem isSquare_mumfordValue_sq_sub_mul_sq (hf : Odd f.natDegree) {p q : K[X]}
    (h : IsCoprime (p ^ 2 - f * q ^ 2) f) : IsSquare (mumfordValue f (p ^ 2 - f * q ^ 2)) := by
  obtain ⟨r, hr⟩ := isSquare_neg_leadingCoeff_pow_mul_leadingCoeff_sq_sub_mul_sq hf p q
  set N := p ^ 2 - f * q ^ 2 with hN
  have hc : IsSquare ((-f.leadingCoeff) ^ N.natDegree * N.leadingCoeff⁻¹) :=
    ⟨r * N.leadingCoeff⁻¹, by grind⟩
  rw [mumfordValue_of_isCoprime f h, map_mul, AdjoinRoot.mk_C]
  convert (hc.map (AdjoinRoot.of f)).mul (IsSquare.sq (AdjoinRoot.mk f p)) using 2
  simp [hN]

-- For `a * a'' = f - v ^ 2` with `f` of odd degree, minus the product of the constants of the
-- values of `a` and `a''` is a square, by the leading coefficient of `v ^ 2 - f * 1 ^ 2`.
private theorem isSquare_neg_mul_of_mul_eq_sub_sq (hf : Odd f.natDegree) {a a'' v : K[X]}
    (h : a * a'' = f - v ^ 2) :
    IsSquare (-((-f.leadingCoeff) ^ a.natDegree * a.leadingCoeff⁻¹ *
      ((-f.leadingCoeff) ^ a''.natDegree * a''.leadingCoeff⁻¹))) := by
  obtain ⟨r, hr⟩ := isSquare_neg_leadingCoeff_pow_mul_leadingCoeff_sq_sub_mul_sq hf v 1
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne a'' 0 with rfl | ha''
  · simp
  rw [one_pow, mul_one, ← neg_sub, ← h, natDegree_neg, leadingCoeff_neg, natDegree_mul ha ha'',
    leadingCoeff_mul] at hr
  exact ⟨r * (a.leadingCoeff * a''.leadingCoeff)⁻¹, by grind [pow_add]⟩

/-- The values of `a` and `a''` with `a * a'' = f - v ^ 2` and `a''` prime to `f` agree modulo
squares; this is the step from `ChabautyColeman.HypJac.descentMap_mumfordClass_of_isCoprime` to
`ChabautyColeman.HypJac.descentMap_mumfordClass`. With the monic `d = gcd a f`, `a = d * a₁` and
`f = d * f₁`, `d` divides `v` (`Squarefree.dvd_of_dvd_of_dvd_sq_sub`), `v = d * v₁`, and the
identity `(a - a₁ * f₁) * a'' = f * (1 + v₁) ^ 2 - (v + f₁) ^ 2` makes the product of the values
a constant times minus a square; the constant is minus a square by
`Polynomial.isSquare_neg_leadingCoeff_pow_mul_leadingCoeff_sq_sub_mul_sq`. -/
theorem isSquare_mumfordValue_mul_of_mul_eq_sub_sq (hsf : Squarefree f) (hf : Odd f.natDegree)
    {a a'' v : K[X]} (h : a * a'' = f - v ^ 2) (ha'' : IsCoprime a'' f) :
    IsSquare (mumfordValue f a * mumfordValue f a'') := by
  obtain ⟨d, a₁, f₁, hd, ha, hf₁, hc⟩ := exists_monic_mul_eq_and_isCoprime (p := a) hsf.ne_zero
  obtain ⟨v₁, rfl⟩ := hsf.dvd_of_dvd_of_dvd_sq_sub ⟨f₁, hf₁.symm⟩
    (dvd_sub_comm.mp (dvd_trans ⟨a₁, ha.symm⟩ ⟨a'', h.symm⟩))
  have h₁ : a₁ * a'' = f₁ - d * v₁ ^ 2 :=
    mul_left_cancel₀ hd.ne_zero (by linear_combination h + a'' * ha - hf₁)
  have hs : AdjoinRoot.mk f (a - a₁ * f₁) * AdjoinRoot.mk f a'' =
      -AdjoinRoot.mk f (d * v₁ + f₁) ^ 2 := by
    rw [← map_mul, ← map_pow, ← map_neg, AdjoinRoot.mk_eq_mk]
    exact ⟨(1 + v₁) ^ 2, by linear_combination (d - f₁) * h₁ - a'' * ha + (1 + v₁) ^ 2 * hf₁⟩
  rw [mumfordValue_eq_of_mul_eq f hd ha hf₁ hc, mumfordValue_of_isCoprime f ha'',
    map_mul (AdjoinRoot.mk f), map_mul (AdjoinRoot.mk f),
    AdjoinRoot.mk_C, AdjoinRoot.mk_C, mul_mul_mul_comm, hs, ← map_mul, ← neg_mul_comm, ← map_neg]
  exact ((isSquare_neg_mul_of_mul_eq_sub_sq f hf h).map (AdjoinRoot.of f)).mul (.sq _)

/-- `ChabautyColeman.mumfordValue` commutes with every homomorphism of fields: the factorization
`a = d * a₁`, `f = d * f₁` of `ChabautyColeman.mumfordValue_eq_of_mul_eq` maps to one over `K'`,
and degrees and leading coefficients are preserved. -/
theorem map_mumfordValue {K' : Type*} [Field K'] (φ : K →+* K') (a : K[X]) :
    AdjoinRoot.map φ f (f.map φ) dvd_rfl (mumfordValue f a) = mumfordValue (f.map φ) (a.map φ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨d, f₁, a₁, hd, hf₁, ha₁, hc⟩ := exists_monic_mul_eq_and_isCoprime (p := f) ha
  rw [mumfordValue_eq_of_mul_eq f hd ha₁ hf₁ hc.symm,
    mumfordValue_eq_of_mul_eq (f.map φ) (hd.map φ) (by rw [← ha₁, Polynomial.map_mul])
      (by rw [← hf₁, Polynomial.map_mul]) ((isCoprime_map φ).mpr hc.symm)]
  simp

/-- For `a` prime to `f` with `a ∣ b ^ 2 - f` and `deg f` odd, the norm of the value `m(a)` is a
square in `K`. With `c = lc(f)` and `k = (-c) ^ deg a * lc(a)⁻¹`, the norm is
`N(m(a)) = k ^ deg f * N(a(θ))`, and `AdjoinRoot.isSquare_mul_norm_mk_of_dvd_sq_sub` makes this a
square, as `deg f` is odd. -/
theorem isSquare_norm_mumfordValue (hf : Odd f.natDegree) {a b : K[X]} (h : a ∣ b ^ 2 - f)
    (ha : IsCoprime a f) : IsSquare (Algebra.norm K (mumfordValue f a)) := by
  have hf₀ : f ≠ 0 := ne_zero_of_natDegree_gt hf.pos
  have hl : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr fun ha₀ ↦
    not_isUnit_of_natDegree_pos f hf.pos (isCoprime_zero_left.mp (ha₀ ▸ ha))
  have hl' : a.leadingCoeff ^ f.natDegree * a.leadingCoeff⁻¹ ^ f.natDegree = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hl, one_pow]
  obtain ⟨t, ht⟩ := AdjoinRoot.isSquare_mul_norm_mk_of_dvd_sq_sub hf₀ h
  rw [mumfordValue_of_isCoprime f ha, map_mul, map_mul,
    AdjoinRoot.norm_mk_C (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf₀))]
  obtain ⟨g, hg⟩ := hf
  refine ⟨f.leadingCoeff ^ (a.natDegree * g) * t * a.leadingCoeff⁻¹ ^ f.natDegree, ?_⟩
  rw [hg] at ht hl' ⊢
  rw [mul_pow, ← pow_mul, neg_pow]
  linear_combination
    (f.leadingCoeff ^ (a.natDegree * g)) ^ 2 * (a.leadingCoeff⁻¹ ^ (2 * g + 1)) ^ 2 * ht -
    (-1) ^ (a.natDegree * (2 * g + 1)) * f.leadingCoeff ^ (a.natDegree * (2 * g + 1)) *
      a.leadingCoeff⁻¹ ^ (2 * g + 1) * Algebra.norm K (AdjoinRoot.mk f a) * hl'

end ChabautyColeman
