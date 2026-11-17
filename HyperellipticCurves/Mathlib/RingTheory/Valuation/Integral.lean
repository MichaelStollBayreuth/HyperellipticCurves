/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: `Polynomial.resultant` and `Polynomial.discr` (statements), subring
-- coefficients and the resultant bounds (proofs).
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Valuation.Integral

import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Resultant.Basic
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Subring

/-!
# Integrality for a valuation, by hand

Concrete forms of the facts that a valuation ring is integrally closed and that a factor of a
unit is a unit, for a valuation `v` on a commutative ring and elements `x` with `v x ≤ 1`.

## Main definitions

* `Polynomial.HasSeparableReduction`: `f` has `v`-integral coefficients and its leading coefficient
  and discriminant are `v`-units, so that its reduction modulo `v` is separable of the same degree.

## Main statements

* `Valuation.eq_one_of_mul_eq_one`: if `v a ≤ 1`, `v b ≤ 1` and `v (a * b) = 1`, then
  `v a = 1`.
* `Valuation.map_eval_eq_of_one_lt`: if the leading coefficient of `p` is a `v`-unit and the
  other coefficients are `v`-integral, then `v (p.eval t) = v t ^ p.natDegree` for `1 < v t`.
* `Valuation.le_one_of_eval_eq_zero`: a root of such a polynomial of positive degree is
  `v`-integral.
* `Valuation.map_sub_eq_one_or_eq_map_eval`: for a `v`-integral root `θ` of `g` at which `g'` is a
  `v`-unit and `v`-integral `x`, `x - θ` is a `v`-unit or has the valuation of `g x`.
* `Valuation.map_derivative_eval_eq_one`, `Valuation.map_resultant_derivative_eq_one`: `g'` is a
  `v`-unit at a `v`-integral root if `Res(g, g')` is a `v`-unit, which holds if the leading
  coefficient and the discriminant are.
* `Valuation.le_one_of_isIntegral`: an element integral over `O` is `v`-integral if the image of
  `O` is.
* `Polynomial.HasSeparableReduction.map`: separable reduction is preserved by a homomorphism of
  fields that maps the `v`-integers to `w`-integers.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`, where the polynomial is
monic), for the valuations of `x₀ - θ` in the point lemma of the `x - T` descent;
upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
  {t a b : R}

/-- If a product of two `v`-integral elements is a `v`-unit, then so is each factor. -/
theorem eq_one_of_mul_eq_one (ha : v a ≤ 1) (hb : v b ≤ 1) (hab : v (a * b) = 1) : v a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ₀) = v a * v b := by rw [← map_mul, hab]
    _ ≤ v a * 1 := by gcongr
    _ = v a := mul_one _

/-- If the leading coefficient of `p` is a `v`-unit, the other coefficients are `v`-integral and
`1 < v t`, then the value of `p` at `t` is dominated by the leading term:
`v (p.eval t) = v t ^ p.natDegree`. In particular, `p.eval t ≠ 0`. -/
theorem map_eval_eq_of_one_lt {p : R[X]} (hlc : v p.leadingCoeff = 1)
    (hcoeff : ∀ i < p.natDegree, v (p.coeff i) ≤ 1) (ht : 1 < v t) :
    v (p.eval t) = v t ^ p.natDegree := by
  set n := p.natDegree
  have h0 : v t ≠ 0 := (zero_lt_one.trans ht).ne'
  have hlt : v (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < v (p.leadingCoeff * t ^ n) := by
    rw [map_mul, hlc, one_mul, map_pow]
    refine v.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc v (p.coeff i * t ^ i) ≤ 1 * v t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = v t ^ i := one_mul _
      _ < v t ^ n := pow_lt_pow_right₀ ht hi
  rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree, v.map_add_eq_of_lt_right hlt,
    map_mul, hlc, one_mul, map_pow]

/-- A root of a polynomial of positive degree whose leading coefficient is a `v`-unit and whose
other coefficients are `v`-integral is itself `v`-integral. -/
theorem le_one_of_eval_eq_zero {p : R[X]} (hlc : v p.leadingCoeff = 1)
    (hcoeff : ∀ i < p.natDegree, v (p.coeff i) ≤ 1) (hdeg : p.natDegree ≠ 0)
    (heq : p.eval t = 0) :
    v t ≤ 1 := by
  by_contra! hlt
  have h := v.map_eval_eq_of_one_lt hlc hcoeff hlt
  rw [heq, map_zero] at h
  exact (zero_lt_one.trans hlt).ne' (pow_eq_zero_iff hdeg |>.mp h.symm)

theorem coeffs_subset_integer {g : R[X]} (hg : ∀ i, v (g.coeff i) ≤ 1) :
    (g.coeffs : Set R) ⊆ v.integer := fun c hc ↦ by
  obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
  exact hg n

/-- If `g` has `v`-integral coefficients, `θ` is a `v`-integral root of `g` at which `g'` is a
`v`-unit and `x` is `v`-integral, then either `x - θ` is a `v`-unit, or it has the valuation of
`g x`: the cofactor of `x - θ` in `g x` is congruent to `g' θ` modulo `x - θ`
(`Polynomial.exists_mem_eval_eq_add_mul`). -/
theorem map_sub_eq_one_or_eq_map_eval {g : R[X]} (hg : ∀ i, v (g.coeff i) ≤ 1) {θ x : R}
    (hθ : g.eval θ = 0) (hθ1 : v θ ≤ 1) (hx : v x ≤ 1) (hd : v (g.derivative.eval θ) = 1) :
    v (x - θ) = 1 ∨ v (x - θ) = v (g.eval x) := by
  obtain ⟨k, hk, he⟩ := exists_mem_eval_eq_add_mul (v.coeffs_subset_integer hg) hθ1 hx
  refine (v.map_sub_le hx hθ1).eq_or_lt.imp id fun hlt ↦ ?_
  rw [he, hθ, zero_add, map_mul, v.map_add_eq_of_lt_left, hd, mul_one]
  rw [hd, map_mul]
  exact (mul_le_of_le_one_left' hk).trans_lt hlt

/-- If `g` has `v`-integral coefficients and `Res(g, g')` is a `v`-unit, then `g'` is a `v`-unit
at every `v`-integral root `θ` of `g`: over the ring of `v`-integers, `g' θ` divides
`Res(g, g')` (`Polynomial.eval_dvd_resultant_of_eval_eq_zero`). -/
theorem map_derivative_eval_eq_one {g : R[X]} (hg : ∀ i, v (g.coeff i) ≤ 1) {θ : R}
    (hθ : g.eval θ = 0) (hθ1 : v θ ≤ 1) (hdeg : g.natDegree ≠ 0)
    (hres : v (g.resultant g.derivative g.natDegree (g.natDegree - 1)) = 1) :
    v (g.derivative.eval θ) = 1 := by
  have hT := v.coeffs_subset_integer hg
  have he (q : v.integer[X]) : v.integer.subtype (q.eval ⟨θ, hθ1⟩) =
      (q.map v.integer.subtype).eval θ := (eval_map_apply ..).symm
  have hd := he (g.toSubring v.integer hT).derivative
  rw [← derivative_map, map_toSubring] at hd
  obtain ⟨c, hc⟩ := eval_dvd_resultant_of_eval_eq_zero (g := g.toSubring v.integer hT)
    (q := (g.toSubring v.integer hT).derivative)
    (Subtype.ext (by simpa [map_toSubring, hθ] using he (g.toSubring v.integer hT)))
    (natDegree_toSubring ..).le
    ((natDegree_derivative_le _).trans (by rw [natDegree_toSubring])) (.inl hdeg)
  have h := congr(v.integer.subtype $hc)
  rw [← resultant_map_map, map_mul, hd, ← derivative_map, map_toSubring] at h
  refine v.eq_one_of_mul_eq_one ?_ c.2 (h ▸ hres)
  rw [← hd]
  exact (eval ⟨θ, hθ1⟩ (g.toSubring v.integer hT).derivative).2

/-- If the discriminant and the leading coefficient of `f` are `v`-units, then so is the resultant
of `f` and `f'`. -/
theorem map_resultant_derivative_eq_one {f : R[X]} (hdeg : 0 < f.degree)
    (hlc : v f.leadingCoeff = 1) (hdisc : v f.discr = 1) :
    v (f.resultant f.derivative f.natDegree (f.natDegree - 1)) = 1 := by
  rw [resultant_deriv hdeg, map_mul, map_mul, map_pow, Valuation.map_neg, map_one, one_pow,
    one_mul, hlc, hdisc, one_mul]

/-- An element integral over `O` has valuation at most `1`, if the image of `O` does. Unlike in
`Valuation.Integers.mem_of_integral`, the image of `O` need not be all of the `v`-integers. -/
theorem le_one_of_isIntegral {O : Type*} [CommRing O] [Algebra O R]
    (h : ∀ c, v (algebraMap O R c) ≤ 1) {x : R} (hx : IsIntegral O x) : v x ≤ 1 :=
  (integer.integers v).isIntegral_iff_v_le_one.mp
    (hx.map_of_comp_eq ((algebraMap O R).codRestrict v.integer h) (RingHom.id R) rfl)

end Valuation

namespace Valuation

variable {K Γ₀ Γ₁ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₁] {v : Valuation K Γ₀} {v' : Valuation K Γ₁}

/-- If the `v`-integers are `v'`-integral, then the `v`-units are `v'`-units. -/
theorem eq_one_of_forall_le_one (h : ∀ c, v c ≤ 1 → v' c ≤ 1) {c : K} (hc : v c = 1) :
    v' c = 1 :=
  have hc0 : c ≠ 0 := v.ne_zero_iff.mp (hc ▸ one_ne_zero)
  (h c hc.le).antisymm <| (v'.one_le_val_iff hc0).mpr <| h _ <| (v.one_le_val_iff hc0).mp hc.ge

end Valuation

namespace Polynomial

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]

/-- A polynomial `f` has *separable reduction* at a valuation `v` if its coefficients are
`v`-integral and its leading coefficient and discriminant are `v`-units, so that its reduction
modulo `v` is separable of the same degree. -/
structure HasSeparableReduction (f : R[X]) (v : Valuation R Γ₀) : Prop where
  /-- The coefficients of `f` are `v`-integral. -/
  coeff_le_one (i : ℕ) : v (f.coeff i) ≤ 1
  /-- The leading coefficient of `f` is a `v`-unit. -/
  leadingCoeff_eq_one : v f.leadingCoeff = 1
  /-- The discriminant of `f` is a `v`-unit. -/
  discr_eq_one : v f.discr = 1

variable {K L Γ₁ : Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero Γ₁]

/-- Separable reduction is preserved by a homomorphism of fields `φ` that maps the `v`-integers to
`w`-integers. -/
theorem HasSeparableReduction.map {f : K[X]} {v : Valuation K Γ₀} (h : f.HasSeparableReduction v)
    {φ : K →+* L} {w : Valuation L Γ₁} (hle : ∀ c, v c ≤ 1 → w (φ c) ≤ 1) :
    (f.map φ).HasSeparableReduction w where
  coeff_le_one i := by rw [coeff_map]; exact hle _ (h.coeff_le_one i)
  leadingCoeff_eq_one := by
    rw [leadingCoeff_map]
    exact v.eq_one_of_forall_le_one (v' := w.comap φ) hle h.leadingCoeff_eq_one
  discr_eq_one := by
    rw [discr_map_of_injective φ.injective]
    exact v.eq_one_of_forall_le_one (v' := w.comap φ) hle h.discr_eq_one

end Polynomial
