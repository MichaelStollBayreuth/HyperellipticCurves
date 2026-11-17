/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Descent.Map

import HyperellipticCurves.Curve.MumfordReduction
import HyperellipticCurves.Descent.Halving
import HyperellipticCurves.Mathlib.Algebra.Polynomial.Degree.Domain
import HyperellipticCurves.Mathlib.Algebra.Polynomial.FieldDivision
import HyperellipticCurves.Mathlib.Algebra.Squarefree.Basic
import HyperellipticCurves.Mathlib.GroupTheory.IndexNSmul
import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot
import HyperellipticCurves.Mathlib.RingTheory.Coprime.Basic
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Basic
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Content
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The kernel of the `x - T` map

For `f` squarefree of odd degree over a field `K` with `2 ≠ 0`, the kernel of the `x - T` map
`ChabautyColeman.HypJac.descentMap` is `2 J(K)`. The inclusion `2 J(K) ⊆ ker μ` is formal; the
converse is the existence half of [Sto17], Proposition 5.1: if `m(a)` is a square, a linear system
has a solution `(u, v, w)` with `w ≠ 0`, and the function `u * y - v * d` of norm `λ * a * w ^ 2`
shows, by a descent on the degree of `w` ending in a halving certificate, that `[a, b]` is twice a
point.

## Main statements

* `ChabautyColeman.exists_sq_mul_eq_mul_sq_sub_mul_sq`: the congruences (6) of [Sto17],
  Proposition 5.1, have a solution with `w ≠ 0`, and it satisfies the relation (8).
* `ChabautyColeman.exists_mumfordClass_eq_sq_of_sq_sub_eq`: a function `U * y - V` of norm
  `λ * a * W ^ 2` with `W ≠ 0` and `V ≡ U * b` modulo the squarefree `a` makes `[a, b]` twice a
  point.
* `ChabautyColeman.exists_mumfordClass_eq_sq_of_isSquare_mumfordValue`: [Sto17], Proposition 5.1,
  existence half.
* `ChabautyColeman.HypJac.ker_descentMap`: the kernel of `μ` is `2 J(K)`.
* `ChabautyColeman.HypJac.ker_descentMap_le_sup`: condition (C0) of [Sto17], Section 2, for
  `d = μ`, `p = 2` and every subgroup `Γ`.
* `ChabautyColeman.HypJac.card_range_descentMap_eq_card_quotient`: the image of `μ` has as many
  elements as `J(K) / 2 J(K)`.
* `ChabautyColeman.HypJac.card_range_descentMap`,
  `ChabautyColeman.HypJac.pow_rank_le_card_of_range_descentMap_le`: the rank formula.

## Implementation notes

The descent replaces the minimal solution of [Sto17]: a common prime factor `p` of `U` and `W`
divides `V`, and `(U / p, V / p, W / p)` is again such a function, for `(a, b)` or, after a sign
change of `b` on `p ∣ a` (`ChabautyColeman.mumfordClass_mul_eq_mul_sq`), for `(a, b')`; when `U`
is prime to `W`, the data form a `ChabautyColeman.HalvingCertificate`.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5
-/

@[expose] public section

open Polynomial
open scoped Matrix

namespace ChabautyColeman

variable {K : Type*} [Field K] (f : K[X])

-- The relation `(8)` modulo `f₁`, `a₁` and `d`, for `a = d * a₁` and `f = d * f₁`, from the
-- squared congruences `(6)`.
private theorem mul_mul_dvd_sq_mul_sub_sub {R : Type*} [CommRing R] {b s d a₁ f₁ u v w l : R}
    (hdf : IsCoprime d f₁) (hda : IsCoprime d a₁) (hc : IsCoprime a₁ f₁)
    (h : d * a₁ ∣ b ^ 2 - d * f₁) (hs : d * f₁ ∣ s ^ 2 - l * (d * a₁ - a₁ * f₁))
    (h₁ : f₁ ∣ v * d - w * s) (h₂ : a₁ ∣ v * d - u * b) (h₃ : d ∣ u * f₁ - w * s) :
    f₁ * a₁ * d ∣ u ^ 2 * f₁ - (d * v ^ 2 - l * a₁ * w ^ 2) := by
  have e₁ : d * (u ^ 2 * f₁ - (d * v ^ 2 - l * a₁ * w ^ 2)) = f₁ * (d * u ^ 2 + l * a₁ * w ^ 2) -
      (v * d - w * s) * (v * d + w * s) - w ^ 2 * (s ^ 2 - l * (d * a₁ - a₁ * f₁)) := by ring
  have e₂ : d * (u ^ 2 * f₁ - (d * v ^ 2 - l * a₁ * w ^ 2)) = (u * b - v * d) * (u * b + v * d) -
      u ^ 2 * (b ^ 2 - d * f₁) + a₁ * (l * d * w ^ 2) := by ring
  have e₃ : f₁ * (u ^ 2 * f₁ - (d * v ^ 2 - l * a₁ * w ^ 2)) = (u * f₁ - w * s) * (u * f₁ + w * s) +
      w ^ 2 * (s ^ 2 - l * (d * a₁ - a₁ * f₁)) + d * (l * a₁ * w ^ 2 - f₁ * v ^ 2) := by ring
  refine (hdf.symm.mul_left hda.symm).mul_dvd (hc.symm.mul_dvd ?_ ?_) ?_
  · refine hdf.symm.dvd_of_dvd_mul_left (e₁ ▸ ?_)
    exact ((dvd_mul_right _ _).sub (h₁.mul_right _)).sub (((dvd_mul_left f₁ d).trans hs).mul_left _)
  · refine hda.symm.dvd_of_dvd_mul_left (e₂ ▸ ?_)
    exact (((dvd_sub_comm.mp h₂).mul_right _).sub
      (((dvd_mul_left a₁ d).trans h).mul_left _)).add (dvd_mul_right _ _)
  · refine hdf.dvd_of_dvd_mul_left (e₃ ▸ ?_)
    exact ((h₃.mul_right _).add (((dvd_mul_right d f₁).trans hs).mul_left _)).add
      (dvd_mul_right _ _)

-- The degree bounds `(7)` make every term of the relation `(8)` of degree `< deg (f₁ * a₁ * d)`.
private theorem sq_mul_sub_sub_mem_degreeLT {d a₁ f₁ u v w : K[X]} {l : K} {g : ℕ}
    (hg : d.natDegree + f₁.natDegree = 2 * g + 1)
    (hu : u ∈ degreeLT K ((d.natDegree + a₁.natDegree + 1) / 2))
    (hv : v ∈ degreeLT K (g + (d.natDegree + a₁.natDegree) / 2 + 1 - d.natDegree))
    (hw : w ∈ degreeLT K (g + 1)) :
    u ^ 2 * f₁ - (d * v ^ 2 - C l * a₁ * w ^ 2) ∈
      degreeLT K (f₁.natDegree + a₁.natDegree + d.natDegree) := by
  have hp := mem_degreeLT_natDegree_add_one (R := K)
  rw [sq, sq, sq, mul_assoc (C l), ← smul_eq_C_mul]
  refine sub_mem (degreeLT_mono ?_ (mul_mem_degreeLT (mul_mem_degreeLT hu hu) (hp f₁)))
    (sub_mem (degreeLT_mono ?_ (mul_mem_degreeLT (hp d) (mul_mem_degreeLT hv hv)))
      (Submodule.smul_mem _ _ (degreeLT_mono ?_
        (mul_mem_degreeLT (hp a₁) (mul_mem_degreeLT hw hw))))) <;> lia

/-- The first claim of [Sto17], Proposition 5.1: the congruences `(6)` have a nonzero solution
`(u, v, w)` under the degree bounds `(7)`, as these allow one more unknown coefficient than there
are linear conditions (`Polynomial.exists_ne_zero_forall_mem_degreeLT_and_dvd_vecMul`). -/
theorem exists_ne_zero_dvd_mul_sub_mul {g : ℕ} (hg : f.natDegree = 2 * g + 1)
    {a d a₁ f₁ : K[X]} (b s : K[X]) (ha : a ≠ 0) (hdeg : a.natDegree ≤ f.natDegree)
    (had : d * a₁ = a) (hfd : d * f₁ = f) :
    ∃ u v w : K[X], (u, v, w) ≠ 0 ∧ u ∈ degreeLT K ((a.natDegree + 1) / 2) ∧
      v ∈ degreeLT K (g + a.natDegree / 2 + 1 - d.natDegree) ∧ w ∈ degreeLT K (g + 1) ∧
      f₁ ∣ v * d - w * s ∧ a₁ ∣ v * d - u * b ∧ d ∣ u * f₁ - w * s := by
  have hf : f ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by lia)
  obtain ⟨hd, hf₁⟩ := mul_ne_zero_iff.mp (hfd ▸ hf)
  have ha₁ := right_ne_zero_of_mul (had ▸ ha)
  have hN : f.natDegree = d.natDegree + f₁.natDegree := hfd ▸ natDegree_mul hd hf₁
  have hn : a.natDegree = d.natDegree + a₁.natDegree := had ▸ natDegree_mul hd ha₁
  obtain ⟨x, hx0, hxd, hx⟩ := exists_ne_zero_forall_mem_degreeLT_and_dvd_vecMul ![f₁, a₁, d]
    (by simp [Fin.forall_fin_succ, *]) !![0, -b, f₁; d, d, 0; -s, 0, -s]
    ![(a.natDegree + 1) / 2, g + a.natDegree / 2 + 1 - d.natDegree, g + 1]
    (by simp [Fin.sum_univ_three]; lia)
  refine ⟨x 0, x 1, x 2, fun h0 ↦ hx0 ?_, hxd 0, hxd 1, hxd 2, ?_, ?_, ?_⟩
  · ext i : 1
    fin_cases i <;> simp_all
  · simpa [Matrix.vecHead, Matrix.vecTail, ← sub_eq_add_neg] using hx 0
  · simpa [Matrix.vecHead, Matrix.vecTail, neg_add_eq_sub] using hx 1
  · simpa [Matrix.vecHead, Matrix.vecTail, ← sub_eq_add_neg] using hx 2

/-- The relation `(8)` of [Sto17], Proposition 5.1, for every solution of the congruences `(6)`
under the degree bounds `(7)`: it holds modulo the pairwise coprime `f₁`, `a₁` and `d`, and all
its terms have degree less than `deg (f₁ * a₁ * d)`. -/
theorem sq_mul_eq_mul_sq_sub_mul_sq (hsf : Squarefree f) {g : ℕ} (hg : f.natDegree = 2 * g + 1)
    {a b s d a₁ f₁ u v w : K[X]} {l : K} (h : a ∣ b ^ 2 - f) (had : d * a₁ = a)
    (hfd : d * f₁ = f) (hc : IsCoprime a₁ f₁) (hs : f ∣ s ^ 2 - C l * (a - a₁ * f₁))
    (h₁ : f₁ ∣ v * d - w * s) (h₂ : a₁ ∣ v * d - u * b) (h₃ : d ∣ u * f₁ - w * s)
    (hu : u ∈ degreeLT K ((a.natDegree + 1) / 2))
    (hv : v ∈ degreeLT K (g + a.natDegree / 2 + 1 - d.natDegree))
    (hw : w ∈ degreeLT K (g + 1)) :
    u ^ 2 * f₁ = d * v ^ 2 - C l * a₁ * w ^ 2 := by
  have ha := ne_zero_of_dvd_sq_sub ⟨g, hg⟩ h
  subst had hfd
  obtain ⟨hd, ha₁⟩ := mul_ne_zero_iff.mp ha
  have hf₁ := right_ne_zero_of_mul hsf.ne_zero
  rw [natDegree_mul hd hf₁] at hg
  rw [natDegree_mul hd ha₁] at hu hv
  rw [← sub_eq_zero]
  refine eq_zero_of_dvd_of_degree_lt (mul_mul_dvd_sq_mul_sub_sub
    (IsRelPrime.of_squarefree_mul hsf).isCoprime
    (hsf.isRelPrime_of_dvd_of_mul_dvd_sq_sub (dvd_mul_right d f₁) h).isCoprime hc h hs h₁ h₂ h₃) ?_
  rw [degree_eq_natDegree (p := f₁ * a₁ * d) (by simp [*]), ← mem_degreeLT,
    natDegree_mul (by simp [*]) hd, natDegree_mul hf₁ ha₁]
  exact sq_mul_sub_sub_mem_degreeLT hg hu hv hw

/-- [Sto17], Proposition 5.1, existence: the congruences `(6)` have a solution with `w ≠ 0` that
satisfies the relation `(8)`; the proposition takes `l = (-lc f) ^ deg a`. A nonzero solution under
the degree bounds `(7)` (`ChabautyColeman.exists_ne_zero_dvd_mul_sub_mul`) satisfies `(8)`
(`ChabautyColeman.sq_mul_eq_mul_sq_sub_mul_sq`), and for `w = 0` the relation reads
`u ^ 2 * f₁ = d * v ^ 2`, whose sides have degrees of different parity unless `u = v = 0`. -/
theorem exists_sq_mul_eq_mul_sq_sub_mul_sq (hsf : Squarefree f) (hf : Odd f.natDegree)
    {a b s d a₁ f₁ : K[X]} {l : K} (hdeg : a.natDegree ≤ f.natDegree) (h : a ∣ b ^ 2 - f)
    (had : d * a₁ = a) (hfd : d * f₁ = f) (hc : IsCoprime a₁ f₁)
    (hs : f ∣ s ^ 2 - C l * (a - a₁ * f₁)) :
    ∃ u v w : K[X], w ≠ 0 ∧ u ^ 2 * f₁ = d * v ^ 2 - C l * a₁ * w ^ 2 ∧
      f₁ ∣ v * d - w * s ∧ a₁ ∣ v * d - u * b ∧ d ∣ u * f₁ - w * s := by
  obtain ⟨g, hg⟩ := id hf
  obtain ⟨u, v, w, hne, hu, hv, hw, h₁, h₂, h₃⟩ :=
    exists_ne_zero_dvd_mul_sub_mul f hg b s (ne_zero_of_dvd_sq_sub hf h) hdeg had hfd
  have hrel := sq_mul_eq_mul_sq_sub_mul_sq f hsf hg h had hfd hc hs h₁ h₂ h₃ hu hv hw
  refine ⟨u, v, w, fun hw0 ↦ hne ?_, hrel, h₁, h₂, h₃⟩
  have hodd : Odd (d * f₁).natDegree := hfd ▸ hf
  have huv : d * v ^ 2 = f₁ * u ^ 2 := by linear_combination -hrel + C l * a₁ * w * hw0
  simp [eq_zero_of_mul_sq_eq_mul_sq hodd huv,
    eq_zero_of_mul_sq_eq_mul_sq (by rwa [mul_comm]) huv.symm, hw0]

-- Modulo a prime divisor `p` of `b ^ 2 - f`, the norm `V ^ 2 - U ^ 2 * f` of `V - U * y` (for
-- `y ^ 2 = f`) is `(V - U * b) * (V + U * b)`.
private theorem _root_.Prime.dvd_sub_mul_or_dvd_add_mul {R : Type*} [CommRing R] {p b f U V : R}
    (hp : Prime p) (h : p ∣ b ^ 2 - f) (h' : p ∣ V ^ 2 - U ^ 2 * f) :
    p ∣ V - U * b ∨ p ∣ V + U * b :=
  hp.dvd_or_dvd ((dvd_sub h' (h.mul_left (U ^ 2))).trans (dvd_of_eq (by ring)))

-- For a prime `p`, `V ^ 2 - (p * U) ^ 2 * f = c * (a * (p * W) ^ 2)` makes `p` divide `V`, and
-- `V / p`, `U` and `W` satisfy the same relation.
private theorem _root_.Prime.exists_eq_mul_and_sq_sub_eq {R : Type*} [CommRing R] [IsDomain R]
    {p a c f U V W : R} (hp : Prime p) (h : V ^ 2 - (p * U) ^ 2 * f = c * (a * (p * W) ^ 2)) :
    ∃ V', V = p * V' ∧ V' ^ 2 - U ^ 2 * f = c * (a * W ^ 2) := by
  obtain ⟨V', rfl⟩ := hp.dvd_of_dvd_pow (a := V) (n := 2)
    ⟨p * U ^ 2 * f + c * a * p * W ^ 2, by linear_combination h⟩
  exact ⟨V', rfl, mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero) (by linear_combination h)⟩

/-- The relation `u ^ 2 * f₁ = d * v ^ 2 - c * a₁ * w ^ 2` of [Sto17], Proposition 5.1, for
`a = d * a₁` and `f = d * f₁` says that the norm of `u * y - v * d` is `c * a * w ^ 2`. -/
theorem sq_sub_eq_of_sq_mul_eq {R : Type*} [CommRing R] {a c d f a₁ f₁ u v w : R}
    (had : d * a₁ = a) (hfd : d * f₁ = f) (h : u ^ 2 * f₁ = d * v ^ 2 - c * a₁ * w ^ 2) :
    (v * d) ^ 2 - u ^ 2 * f = c * (a * w ^ 2) := by
  linear_combination (-d) * h + u ^ 2 * hfd + c * w ^ 2 * had

/-- The coefficient `U` of a function `U * y - V` with norm `c * a * W ^ 2`, `c` a unit, and
`V ≡ U * b` modulo the squarefree `a` is prime to `a * W ^ 2` once it is prime to `W`: a prime `p`
dividing `U` and `a` divides `V`, so `p ^ 2` divides `a * W ^ 2`, and `p` divides `W`. -/
theorem isCoprime_mul_sq_of_sq_sub_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {a b c f U V W : R} (hc : IsUnit c) (hsq : Squarefree a)
    (hrel : V ^ 2 - U ^ 2 * f = c * (a * W ^ 2)) (hV : a ∣ V - U * b) (hUW : IsCoprime U W) :
    IsCoprime U (a * W ^ 2) := by
  refine .mul_right (isCoprime_of_prime_dvd (fun h ↦ hsq.ne_zero h.2) fun p hp hpU hpa ↦ ?_)
    hUW.pow_right
  have hpV : p ∣ V := (dvd_sub_left (hpU.mul_right b)).mp (hpa.trans hV)
  have hpW : ¬p ∣ W ^ 2 := fun h ↦ hp.not_isUnit (hUW.isUnit_of_dvd' hpU (hp.dvd_of_dvd_pow h))
  have h2 : p ^ 2 ∣ a * W ^ 2 := hc.dvd_mul_left.mp
    (hrel ▸ dvd_sub (pow_dvd_pow_of_dvd hpV 2) ((pow_dvd_pow_of_dvd hpU 2).mul_right f))
  exact hp.not_isUnit (hsq p (sq p ▸ hp.pow_dvd_of_dvd_mul_right 2 hpW h2))

variable [Fact (Odd f.natDegree)] [NeZero (2 : K)] [Fact (Squarefree f)]

/-- The class of `(a, b)` is twice the class of `(W, R)` for some `R` if `U * y - V` has norm
`lam * a * W ^ 2`, `V ≡ U * b` modulo `a`, and `U` is prime to `a * W ^ 2`: these are the data of
a halving certificate (`ChabautyColeman.HalvingCertificate.mumfordClass_eq_sq`) with
`R = -(e * V)` for the Bézout cofactor `e` of `U`. -/
theorem exists_mumfordClass_eq_sq_of_isCoprime {a b U V W : K[X]} {lam : K} (hlam : lam ≠ 0)
    (hrel : V ^ 2 - U ^ 2 * f = C lam * (a * W ^ 2)) (hV : a ∣ V - U * b)
    (hc : IsCoprime U (a * W ^ 2)) : ∃ R, mumfordClass f a b = mumfordClass f W R ^ 2 := by
  obtain ⟨e, e', he⟩ := hc
  exact ⟨-(e * V), (HalvingCertificate.mk U V e e' lam hlam hrel hV
    ⟨V * e' * a * W, by linear_combination (-V) * he⟩ he).mumfordClass_eq_sq⟩

/-- Changing the sign of the second polynomial `b` on the factor `t` of `a * t`, with `a` and `t`
coprime: the Chinese remainder theorem gives `b'` with `b' ≡ b` modulo `a` and `b' ≡ -b` modulo
`t`, which turns the congruences `V ≡ U * b` modulo `a` and `V ≡ -U * b` modulo `t` into
`V ≡ U * b'` modulo `a * t`, and `ChabautyColeman.mumfordClass_mul_eq_mul_sq` relates the
classes. -/
theorem exists_mumfordClass_mul_eq_mul_sq {a t b U V : K[X]} (hc : IsCoprime a t)
    (h : a * t ∣ b ^ 2 - f) (h₁ : a ∣ V - U * b) (h₂ : t ∣ V + U * b) :
    ∃ b', a * t ∣ b' ^ 2 - f ∧ a * t ∣ V - U * b' ∧
      mumfordClass f (a * t) b = mumfordClass f (a * t) b' * mumfordClass f t b ^ 2 := by
  obtain ⟨b', hb₁, hb₂⟩ := hc.exists_dvd_sub_and_dvd_sub b (-b)
  rw [sub_neg_eq_add] at hb₂
  have h' := dvd_sq_sub_of_dvd_sub_of_dvd_add h hb₁ hb₂
  refine ⟨b', h', hc.mul_dvd ?_ ?_, mumfordClass_mul_eq_mul_sq f h hb₁ hb₂⟩
  · exact (dvd_sub h₁ (hb₁.mul_left U)).trans (dvd_of_eq (by ring))
  · exact (dvd_sub h₂ (hb₂.mul_left U)).trans (dvd_of_eq (by ring))

/-- One step of the descent of [Sto17], Proposition 5.1: for a prime `p` with
`p * V ≡ p * U * b` modulo the squarefree `a`, either `V ≡ U * b` modulo `a`, or `p` divides `a`
and the sign change on `p` (`ChabautyColeman.exists_mumfordClass_mul_eq_mul_sq`) gives `b'` with
`V ≡ U * b'` modulo `a`, whose class differs from that of `(a, b)` by twice the class of
`(p, b)`. -/
theorem exists_mumfordClass_eq_mul_sq_of_dvd_mul {a b p U V : K[X]} (hsq : Squarefree a)
    (hp : Prime p) (h : a ∣ b ^ 2 - f) (hN : a ∣ V ^ 2 - U ^ 2 * f) (hV : a ∣ p * (V - U * b)) :
    ∃ b', a ∣ b' ^ 2 - f ∧ a ∣ V - U * b' ∧
      ∃ Q : HypJac K f, mumfordClass f a b = mumfordClass f a b' * Q ^ 2 := by
  by_cases hpa : p ∣ a
  · obtain ⟨a', rfl⟩ := exists_eq_mul_left_of_dvd hpa
    have hc : IsCoprime a' p := (IsRelPrime.of_squarefree_mul hsq).isCoprime
    have h₁ : a' ∣ V - U * b := (mul_dvd_mul_iff_left hp.ne_zero).mp (mul_comm a' p ▸ hV)
    rcases hp.dvd_sub_mul_or_dvd_add_mul ((dvd_mul_left p a').trans h)
      ((dvd_mul_left p a').trans hN) with h₂ | h₂
    · exact ⟨b, h, hc.mul_dvd h₁ h₂, 1, by simp⟩
    · obtain ⟨b', h', hV', hQ⟩ := exists_mumfordClass_mul_eq_mul_sq f hc h h₁ h₂
      exact ⟨b', h', hV', _, hQ⟩
  · exact ⟨b, h, (hp.coprime_iff_not_dvd.mpr hpa).symm.dvd_of_dvd_mul_left hV, 1, by simp⟩

/-- **[Sto17], Proposition 5.1**, the descent: a function `U * y - V` with norm `lam * a * W ^ 2`,
`W ≠ 0`, and `V ≡ U * b` modulo the squarefree `a` shows that the class of `(a, b)` is twice a
point. By induction on the degree of `W`: if `U` is prime to `W`, a halving certificate exists
(`ChabautyColeman.exists_mumfordClass_eq_sq_of_isCoprime`); otherwise a common prime factor `p` of
`U` and `W` divides `V`, and `(U / p, V / p, W / p)` is such a function for `(a, b)` or, after a
sign change on `p` (`ChabautyColeman.exists_mumfordClass_eq_mul_sq_of_dvd_mul`), for `(a, b')`. -/
theorem exists_mumfordClass_eq_sq_of_sq_sub_eq {a b U V W : K[X]} {lam : K} (hlam : lam ≠ 0)
    (hsq : Squarefree a) (h : a ∣ b ^ 2 - f) (hW : W ≠ 0)
    (hrel : V ^ 2 - U ^ 2 * f = C lam * (a * W ^ 2)) (hV : a ∣ V - U * b) :
    ∃ Q : HypJac K f, mumfordClass f a b = Q ^ 2 := by
  obtain ⟨n, hn⟩ : ∃ n, W.natDegree = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing b U V W with
  | _ n ih =>
    by_cases hc : IsCoprime U W
    · obtain ⟨R, hR⟩ := exists_mumfordClass_eq_sq_of_isCoprime f hlam hrel hV
        (isCoprime_mul_sq_of_sq_sub_eq (isUnit_C.mpr hlam.isUnit) hsq hrel hV hc)
      exact ⟨_, hR⟩
    obtain ⟨p, hp, ⟨U', rfl⟩, ⟨W', rfl⟩⟩ : ∃ p, Prime p ∧ p ∣ U ∧ p ∣ W := by
      by_contra! H
      exact hc (isCoprime_of_prime_dvd (fun h' ↦ hW h'.2) H)
    obtain ⟨V', rfl, hrel'⟩ := hp.exists_eq_mul_and_sq_sub_eq hrel
    have hW' : W' ≠ 0 := right_ne_zero_of_mul hW
    obtain ⟨b', h', hV', Q, hQ⟩ := exists_mumfordClass_eq_mul_sq_of_dvd_mul f hsq hp h
      (hrel' ▸ (dvd_mul_right a _).mul_left _) (by rwa [mul_sub, ← mul_assoc])
    have hlt : W'.natDegree < n := by
      rw [← hn, natDegree_mul hp.ne_zero hW']
      lia [hp.irreducible.natDegree_pos]
    obtain ⟨Q', hQ'⟩ := ih _ hlt h' hW' hrel' hV' rfl
    exact ⟨Q' * Q, by rw [hQ, hQ', mul_pow]⟩

/-- **[Sto17], Proposition 5.1**, existence half: for `a` squarefree with `deg a ≤ deg f` and
`a ∣ b ^ 2 - f`, if the value `m(a)` is a square in `AdjoinRoot f`, then the class of `(a, b)` is
twice a point. The linear system of [Sto17] has a solution `(u, v, w)` with `w ≠ 0`
(`ChabautyColeman.exists_sq_mul_eq_mul_sq_sub_mul_sq`), and `u * y - v * d` is a function as in
`ChabautyColeman.exists_mumfordClass_eq_sq_of_sq_sub_eq`. [Sto17] takes `a` monic; in general
the factor `lc(a)⁻¹` of `m(a)` enters the constant `lam` of that theorem. -/
theorem exists_mumfordClass_eq_sq_of_isSquare_mumfordValue {a b : K[X]} (hsq : Squarefree a)
    (hdeg : a.natDegree ≤ f.natDegree) (h : a ∣ b ^ 2 - f) (hs : IsSquare (mumfordValue f a)) :
    ∃ Q : HypJac K f, mumfordClass f a b = Q ^ 2 := by
  have hsf : Squarefree f := Fact.out
  obtain ⟨d, a₁, f₁, hd, had, hfd, hc⟩ := exists_monic_mul_eq_and_isCoprime (p := a) hsf.ne_zero
  rw [mumfordValue_eq_of_mul_eq f hd had hfd hc, AdjoinRoot.isSquare_mk_iff] at hs
  obtain ⟨s, hs⟩ := hs
  obtain ⟨u, v, w, hw, hrel, -, hv, -⟩ :=
    exists_sq_mul_eq_mul_sq_sub_mul_sq f hsf Fact.out hdeg h had hfd hc hs
  have hdb : d ∣ b := hsf.dvd_of_dvd_of_dvd_sq_sub (Dvd.intro _ hfd) ((Dvd.intro _ had).trans h)
  have hda : IsCoprime d a₁ := (IsRelPrime.of_squarefree_mul (had ▸ hsq)).isCoprime
  exact exists_mumfordClass_eq_sq_of_sq_sub_eq f (by simp [hsf.ne_zero, hsq.ne_zero]) hsq h hw
    (sq_sub_eq_of_sq_mul_eq had hfd hrel)
    (had ▸ hda.mul_dvd (dvd_sub (dvd_mul_left d v) (hdb.mul_left u)) hv)

/-- The class of a Mumford pair `(a, b)` with `a` squarefree of degree at most `deg f` and
`μ([a, b]) = 1` is a square: the formula `ChabautyColeman.HypJac.descentMap_mumfordClass` makes
`ChabautyColeman.mumfordValue f a` a square, and
`ChabautyColeman.exists_mumfordClass_eq_sq_of_isSquare_mumfordValue` applies. -/
theorem exists_mumfordClass_eq_sq_of_squarefree_of_descentMap_eq_one {a b : K[X]}
    (hsq : Squarefree a) (hdeg : a.natDegree ≤ f.natDegree) (h : a ∣ b ^ 2 - f)
    (hμ : HypJac.descentMap f (mumfordClass f a b) = 1) :
    ∃ Q : HypJac K f, mumfordClass f a b = Q ^ 2 := by
  have hu := isUnit_mumfordValue f Fact.out h
  rw [HypJac.descentMap_mumfordClass f h hu.unit_spec, Units.ModPow.mk_eq_one_iff_isSquare,
    IsUnit.unit_spec] at hμ
  exact exists_mumfordClass_eq_sq_of_isSquare_mumfordValue f hsq hdeg h hμ

/-- The class of a Mumford pair `(a, b)` with `deg a ≤ deg f` and `μ([a, b]) = 1` is a square:
with `a = e ^ 2 * d` and `d` squarefree, `[a, b] = [e, b] ^ 2 * [d, b]` and
`ChabautyColeman.exists_mumfordClass_eq_sq_of_squarefree_of_descentMap_eq_one` applies to
`(d, b)`. -/
theorem exists_mumfordClass_eq_sq_of_descentMap_eq_one {a b : K[X]}
    (hdeg : a.natDegree ≤ f.natDegree) (h : a ∣ b ^ 2 - f)
    (hμ : HypJac.descentMap f (mumfordClass f a b) = 1) :
    ∃ Q : HypJac K f, mumfordClass f a b = Q ^ 2 := by
  obtain ⟨e, d, rfl, hd⟩ := exists_sq_mul_squarefree a
  have he : e ^ 2 ∣ b ^ 2 - f := dvd_of_mul_right_dvd h
  have hd' : d ∣ b ^ 2 - f := dvd_of_mul_left_dvd h
  rw [mumfordClass_mul f h, mumfordClass_pow f he, map_mul, map_pow,
    Units.ModPow.pow_eq_one, one_mul] at hμ
  obtain ⟨Q, hQ⟩ := exists_mumfordClass_eq_sq_of_squarefree_of_descentMap_eq_one f hd
    ((natDegree_le_of_dvd (dvd_mul_left d _) (ne_zero_of_dvd_ne_zero (sq_sub_ne_zero f b) h)).trans
      hdeg) hd' hμ
  exact ⟨mumfordClass f e b * Q, by rw [mumfordClass_mul f h, mumfordClass_pow f he, hQ, mul_pow]⟩

/-- **The kernel of the `x - T` map** is `2 J(K)`, [Sto17], Proposition 5.1: a point in the kernel
has a reduced Mumford representative (`ChabautyColeman.exists_mk0_mumfordIdeal_reduced`), and
`ChabautyColeman.exists_mumfordClass_eq_sq_of_descentMap_eq_one` applies. -/
theorem HypJac.ker_descentMap : (HypJac.descentMap f).ker = (powMonoidHom 2).range := by
  refine le_antisymm ?_ ?_
  · intro P hP
    obtain ⟨a, b, hm, -, hdeg, h, rfl⟩ := exists_mk0_mumfordIdeal_reduced f P
    rw [← mumfordClass_eq_mk0] at hP ⊢
    obtain ⟨Q, hQ⟩ := exists_mumfordClass_eq_sq_of_descentMap_eq_one f (by lia) h hP
    exact ⟨Q, hQ.symm⟩
  · rintro _ ⟨Q, rfl⟩
    simp [MonoidHom.mem_ker]

/-- Condition (C0) of [Sto17], Section 2, for `d = μ` and `p = 2`, for every subgroup `Γ`: the
kernel of `μ` is `2 J(K)` (`ChabautyColeman.HypJac.ker_descentMap`). -/
theorem HypJac.ker_descentMap_le_sup (Γ : Subgroup (HypJac K f)) :
    (HypJac.descentMap f).ker ≤ Γ ⊔ (powMonoidHom 2).range :=
  (ker_descentMap f).le.trans le_sup_right

/-- The image of the `x - T` map is isomorphic to `J(K) / 2 J(K)`
(`ChabautyColeman.HypJac.ker_descentMap`), so it has as many elements. -/
theorem HypJac.card_range_descentMap_eq_card_quotient :
    Nat.card (descentMap f).range =
      Nat.card (HypJac K f ⧸ (powMonoidHom 2 : HypJac K f →* HypJac K f).range) := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, ker_descentMap]

/-- **The rank formula**: for `J(K)` finitely generated of rank `r`, the image of the `x - T` map
has `2 ^ r * #J(K)[2]` elements, as it is isomorphic to `J(K) / 2 J(K)`
(`ChabautyColeman.HypJac.ker_descentMap`), whose order `CommGroup.card_modPow` computes. -/
theorem HypJac.card_range_descentMap [IsMulFG (HypJac K f)] :
    Nat.card (descentMap f).range =
      2 ^ Module.finrank ℤ (Additive (HypJac K f)) *
        Nat.card (powMonoidHom 2 : HypJac K f →* HypJac K f).ker := by
  rw [card_range_descentMap_eq_card_quotient]
  exact CommGroup.card_modPow _ two_ne_zero

/-- The bound of `2`-descent: for `J(K)` finitely generated of rank `r` and a finite subgroup `S`
of `L^× / (L^×)^2` containing the image of the `x - T` map, `2 ^ r * #J(K)[2] ≤ #S`. -/
theorem HypJac.pow_rank_le_card_of_range_descentMap_le [IsMulFG (HypJac K f)]
    {S : Subgroup (Units.ModPow (AdjoinRoot f) 2)} [Finite S] (h : (descentMap f).range ≤ S) :
    2 ^ Module.finrank ℤ (Additive (HypJac K f)) *
        Nat.card (powMonoidHom 2 : HypJac K f →* HypJac K f).ker ≤ Nat.card S :=
  card_range_descentMap f ▸ Subgroup.card_le_of_le h

end ChabautyColeman

end
