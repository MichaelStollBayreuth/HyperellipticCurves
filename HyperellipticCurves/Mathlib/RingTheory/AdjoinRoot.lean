/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.AdjoinRoot

import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Basic
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Quotient

/-!
# Units, squares and quadratic extensions in `AdjoinRoot`

## Main definitions

* `AdjoinRoot.degreeLTEquiv`: for monic `g`, `mk g` as a linear equivalence from the polynomials
  of degree `< deg g` onto `R[X] ⧸ (g)`.

## Main statements

* `AdjoinRoot.map_mk`: `AdjoinRoot.map` on the image of a polynomial.
* `AdjoinRoot.algEquivOfAssociated_mk`: `AdjoinRoot.algEquivOfAssociated` on the image of a
  polynomial.
* `AdjoinRoot.isUnit_mk_iff`: the image of `g` in `R[X] ⧸ (f)` is a unit if and only if `g` is
  prime to `f`.
* `AdjoinRoot.isUnit_of_sub_root_iff`, `AdjoinRoot.isUnit_of_sub_root`: `x₀ - θ` is a unit of
  `K[X] ⧸ (f)` if and only if `f x₀ ≠ 0`.
* `AdjoinRoot.isSquare_mk_iff`: the image of `g` is a square if and only if `g` is a square
  modulo `f`.
* `AdjoinRoot.liftAlgHom_map`: evaluation at a root commutes with base change.
* `AdjoinRoot.liftAlgHom_map_eq_lift`: evaluation at a root `b` of `f.map φ` after base change
  along `φ` is `AdjoinRoot.lift φ b`.
* `AdjoinRoot.exists_eq_of_add_of_mul_root`, `AdjoinRoot.of_add_of_mul_root_eq_zero_iff`: for monic
  `f` of degree `2`, every element of `R[X] ⧸ (f)` is `a + b θ`, uniquely.
* `AdjoinRoot.exists_eq_sq_add_mul_sq_of_isSquare`: if `u + w θ` is a square in
  `R[X] ⧸ (X ^ 2 + b X + c)`, then `4 u - 2 b w = α ^ 2 + (b ^ 2 - 4 c) β ^ 2` and `w = α β`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial

namespace AdjoinRoot

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {p : K[X]} {P : R[X]} {c : K}

@[simp]
theorem mk_modByMonic (g f : R[X]) : mk g (f %ₘ g) = mk g f := by
  by_cases hg : g.Monic
  · rw [← modByMonicHom_mk hg, mk_leftInverse hg]
  · rw [modByMonic_eq_of_not_monic f hg]

@[simp]
theorem map_mk {S : Type*} [CommRing S] (σ : R →+* S) {p : R[X]} {q : S[X]} (hq : q ∣ p.map σ)
    (g : R[X]) :
    map σ p q hq (mk p g) = mk q (g.map σ) := by
  rw [map, lift_mk, ← eval₂_map, ← algebraMap_eq, ← aeval_def, aeval_eq]

theorem isUnit_mk_iff {f g : R[X]} : IsUnit (mk f g) ↔ IsCoprime g f := by
  refine ⟨fun h ↦ ?_, fun ⟨u, v, h⟩ ↦ .of_mul_eq_one_right (mk f u) ?_⟩
  · obtain ⟨u, hu⟩ := isUnit_iff_exists_inv'.mp h
    obtain ⟨u, rfl⟩ := mk_surjective u
    obtain ⟨v, hv⟩ := mk_eq_mk.mp (by simpa using hu : mk f (u * g) = mk f 1)
    exact ⟨u, -v, by linear_combination hv⟩
  · simpa using congr(mk f $h)

/-- `x₀ - θ` is a unit of `K[X] ⧸ (f)`, `θ` the root, if and only if `f x₀ ≠ 0`. -/
theorem isUnit_of_sub_root_iff {K : Type*} [Field K] {f : K[X]} {x₀ : K} :
    IsUnit (of f x₀ - root f) ↔ f.eval x₀ ≠ 0 := by
  rw [← mk_C, ← mk_X, ← map_sub, isUnit_mk_iff, ← neg_sub, IsCoprime.neg_left_iff,
    (irreducible_X_sub_C x₀).coprime_iff_not_dvd, dvd_iff_isRoot]
  rfl

theorem isUnit_of_sub_root {K : Type*} [Field K] {f : K[X]} {x₀ : K} (h0 : f.eval x₀ ≠ 0) :
    IsUnit (of f x₀ - root f) :=
  isUnit_of_sub_root_iff.mpr h0

theorem isSquare_mk_iff {f g : R[X]} :
    IsSquare (mk f g) ↔ ∃ s, f ∣ s ^ 2 - g := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun ⟨s, hs⟩ ↦ ⟨mk f s, ?_⟩⟩
  · obtain ⟨s, rfl⟩ := mk_surjective r
    exact ⟨s, sq s ▸ dvd_sub_comm.mp (mk_eq_mk.mp (hr.trans (map_mul ..).symm))⟩
  · rwa [← map_mul, mk_eq_mk, ← sq, dvd_sub_comm]

section degreeLT

variable [Nontrivial R] {g : R[X]}

/-- For monic `g`, `AdjoinRoot.mk g` is a linear equivalence from the polynomials of degree
`< g.natDegree` onto `AdjoinRoot g`; its inverse is reduction modulo `g`,
`AdjoinRoot.modByMonicHom hg`. -/
noncomputable def degreeLTEquiv (hg : g.Monic) : degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g where
  __ := (mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype
  invFun x := ⟨modByMonicHom hg x, by
    obtain ⟨q, rfl⟩ := mk_surjective x
    exact modByMonic_mem_degreeLT hg q⟩
  left_inv q := by
    ext : 1
    exact (modByMonic_eq_self_iff hg).mpr ((mem_degreeLT_natDegree_iff hg.ne_zero).mp q.2)
  right_inv := mk_leftInverse hg

@[simp]
theorem degreeLTEquiv_apply (hg : g.Monic) (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  rfl

end degreeLT

section Associated

variable {S : Type*} [CommRing S] [Algebra R S]

@[simp]
theorem algEquivOfAssociated_mk {f g : S[X]} (hfg : Associated f g) (p : S[X]) :
    algEquivOfAssociated R f g hfg (mk f p) = mk g p := by
  simp [coe_algEquivOfAssociated, algHomOfDvd]

end Associated

end AdjoinRoot

namespace AdjoinRoot

variable {K K' : Type*} [Field K] [Field K'] {f : K[X]}

/-- Evaluation at a root commutes with base change along `φ : K →+* K'`. -/
theorem liftAlgHom_map (φ : K →+* K') {a : K} {b : K'} (ha : f.IsRoot a)
    (hb : (f.map φ).IsRoot b) (hab : φ a = b) (x : AdjoinRoot f) :
    liftAlgHom (f.map φ) (Algebra.ofId K' K') b (by simpa using hb)
        (map φ f (f.map φ) dvd_rfl x) =
      φ (liftAlgHom f (Algebra.ofId K K) a (by simpa using ha) x) := by
  induction x using AdjoinRoot.induction_on with | ih g => ?_
  simp [← hab, eval_map]

/-- Evaluation at a root `b` of `f.map φ` after base change along `φ : K →+* K'` is evaluation of
`K[X] ⧸ (f)` at `b` along `φ`. -/
theorem liftAlgHom_map_eq_lift (φ : K →+* K') {b : K'} (hb : (f.map φ).IsRoot b)
    (x : AdjoinRoot f) :
    liftAlgHom (f.map φ) (Algebra.ofId K' K') b (by simpa using hb)
        (map φ f (f.map φ) dvd_rfl x) =
      lift φ b (by simpa [eval_map] using hb) x := by
  induction x using AdjoinRoot.induction_on with | ih g => ?_
  simp [lift_mk, eval₂_map]

end AdjoinRoot

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {f : R[X]}

/-- For monic `f` of degree at most `2`, every element of `R[X] ⧸ (f)` is `a + b θ`, `θ` the
root: reduce a representative modulo `f`. -/
theorem exists_eq_of_add_of_mul_root [Nontrivial R] (hf : f.Monic) (hdeg : f.natDegree ≤ 2)
    (z : AdjoinRoot f) : ∃ a b : R, z = of f a + of f b * root f := by
  obtain ⟨q, rfl⟩ := mk_surjective z
  have h1 : (q %ₘ f).degree ≤ 1 :=
    Order.le_of_lt_succ ((degree_modByMonic_lt q hf).trans_le (degree_le_of_natDegree_le hdeg))
  rw [← mk_modByMonic, eq_X_add_C_of_degree_le_one h1]
  exact ⟨(q %ₘ f).coeff 0, (q %ₘ f).coeff 1, by simp [add_comm]⟩

/-- For monic `f` of degree at least `2`, `1` and the root `θ` are linearly independent over `R`
in `R[X] ⧸ (f)`. -/
theorem of_add_of_mul_root_eq_zero_iff (hf : f.Monic) (hdeg : 1 < f.natDegree) {a b : R} :
    of f a + of f b * root f = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hb⟩ ↦ by simp [ha, hb]⟩
  rw [← mk_C, ← mk_C, ← mk_X, ← map_mul, ← map_add, mk_eq_zero, add_comm] at h
  have h0 : C b * X + C a = 0 := by
    by_contra hne
    exact hf.not_dvd_of_degree_lt hne (degree_lt_degree (natDegree_linear_le.trans_lt hdeg)) h
  exact ⟨by simpa using congr(coeff $h0 0), by simpa using congr(coeff $h0 1)⟩

/-- If `u + w θ` is a square in `R[X] ⧸ (X ^ 2 + b X + c)`, `θ` the root, then
`4 u - 2 b w = α ^ 2 + (b ^ 2 - 4 c) β ^ 2` and `w = α β` for some `α` and `β`: for
`(a + a' θ) ^ 2 = u + w θ`, take `α = 2 a - b a'` and `β = a'`. -/
theorem exists_eq_sq_add_mul_sq_of_isSquare [Nontrivial R] {b c u w : R}
    (hf : f = X ^ 2 + C b * X + C c) (h : IsSquare (of f u + of f w * root f)) :
    ∃ α β : R, 4 * u - 2 * b * w = α ^ 2 + (b ^ 2 - 4 * c) * β ^ 2 ∧ w = α * β := by
  subst hf
  have hm : (X ^ 2 + C b * X + C c).Monic := by monicity!
  have hd : (X ^ 2 + C b * X + C c).natDegree = 2 := by compute_degree!
  obtain ⟨z, hz⟩ := h
  obtain ⟨a, a', rfl⟩ := exists_eq_of_add_of_mul_root hm hd.le z
  have hθ := eval₂_root (X ^ 2 + C b * X + C c)
  simp only [eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X] at hθ
  have key : of _ (a ^ 2 - c * a' ^ 2 - u) + of _ (2 * a * a' - b * a' ^ 2 - w) *
      root (X ^ 2 + C b * X + C c) = 0 := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination -hz - (of _ a') ^ 2 * hθ
  obtain ⟨h1, h2⟩ := (of_add_of_mul_root_eq_zero_iff hm (by lia)).mp key
  exact ⟨2 * a - b * a', a', by linear_combination -4 * h1 + 2 * b * h2, by linear_combination -h2⟩

end AdjoinRoot

end
