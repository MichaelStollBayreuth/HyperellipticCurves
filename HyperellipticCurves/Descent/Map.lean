/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.MumfordClass
public import HyperellipticCurves.Curve.MumfordValue
public import HyperellipticCurves.Mathlib.GroupTheory.QuotientGroup.UnitsModPow

import HyperellipticCurves.Curve.MumfordReduction
import HyperellipticCurves.Mathlib.Algebra.Polynomial.FieldDivision
import HyperellipticCurves.Mathlib.RingTheory.Coprime.Basic

/-!
# The `x - T` map

Let `K` be a field in which `2 ≠ 0`, let `f : K[X]` be squarefree of odd degree, and let
`L = AdjoinRoot f`. The `x - T` map `μ : J(K) → L^× / (L^×)^2` of 2-descent ([Sto17], Section 5)
maps the class of a Mumford pair `(a, b)` with `a` prime to `f` to the class of the value
`ChabautyColeman.mumfordValue f a`. This file defines it as a homomorphism.

## Main definitions

* `ChabautyColeman.HypJac.descentMap`: the `x - T` map
  `HypJac K f →* Units.ModPow (AdjoinRoot f) 2`.

## Main statements

* `ChabautyColeman.HypJac.exists_isCoprime_mumfordClass_eq`: every point is a Mumford class whose
  first polynomial is prime to `f * g`, for any `g ≠ 0`.
* `ChabautyColeman.isSquare_mumfordValue_mul_of_mumfordClass_eq`: two representatives prime to `f`
  of one class have values whose product is a square.
* `ChabautyColeman.HypJac.descentMap_mumfordClass_of_isCoprime`: the value of `μ` at the class of
  `(a, b)` with `a` prime to `f`.
* `ChabautyColeman.HypJac.descentMap_mumfordClass`: the formula, `μ([a, b])` is the class of
  `ChabautyColeman.mumfordValue f a` for every Mumford pair.
* `ChabautyColeman.HypJac.map_descentMap`, `ChabautyColeman.HypJac.map_comp_descentMap`: base
  change along a field extension.
* `ChabautyColeman.HypJac.descentMap_mumfordClass_zero_of_mul_eq`: the values at the points
  `[a, 0]` of order dividing `2`, `a * e = f`.
* `ChabautyColeman.HypJac.map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero_of_ne`,
  `ChabautyColeman.HypJac.map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero_self`: the
  components of the value at a point `(a, 0)` at the roots of `f`.
* `ChabautyColeman.HypJac.descentMap_mumfordClass_X_sub_C`: the value at a point `(x₀, y₀)`
  with `f(x₀) ≠ 0`, the class of `lc(f) * (x₀ - θ)`.
* `ChabautyColeman.HypJac.descentMap_mem_ker_norm`: the norm condition.

## Implementation notes

`ChabautyColeman.HypJac.descentMap` is defined by a choice of representatives prime to `f`, in a
section that does not expose it; later proofs use
`ChabautyColeman.HypJac.descentMap_mumfordClass_of_isCoprime` only. Values are stated for any unit
`u` with `↑u = ChabautyColeman.mumfordValue f a`, so that no `IsUnit` proof enters a statement.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K] (f : K[X]) [Fact (Odd f.natDegree)] [NeZero (2 : K)]
  [Fact (Squarefree f)]

/-- Every point of the Jacobian is a Mumford class whose first polynomial is prime to `f * g`, for
any `g ≠ 0`: `ChabautyColeman.exists_mk0_mumfordIdeal_reduced` and the moving lemma
`ChabautyColeman.exists_isCoprime_mumfordClass_eq`. -/
theorem HypJac.exists_isCoprime_mumfordClass_eq (x : HypJac K f) {g : K[X]} (hg : g ≠ 0) :
    ∃ a b, a ∣ b ^ 2 - f ∧ IsCoprime a (f * g) ∧ mumfordClass f a b = x := by
  obtain ⟨u, v, hm, -, -, hdvd, rfl⟩ := exists_mk0_mumfordIdeal_reduced f x
  obtain ⟨a, b, h, ha, he⟩ := ChabautyColeman.exists_isCoprime_mumfordClass_eq f hdvd hg
  exact ⟨a, b, h, ha, he.symm.trans (mumfordClass_eq_mk0 f _)⟩

/-- **Well-definedness** of the `x - T` map on representatives prime to `f`: if `(a, b)` and
`(a', b')` have the same class, then `a * a'` is associated with a norm `p ^ 2 - f * q ^ 2`
(`ChabautyColeman.exists_associated_sq_sub_mul_sq_of_mumfordClass_eq`), so the product of the values
is the value of that norm, a square by `ChabautyColeman.isSquare_mumfordValue_sq_sub_mul_sq`. -/
theorem isSquare_mumfordValue_mul_of_mumfordClass_eq {a b a' b' : K[X]} (h : a ∣ b ^ 2 - f)
    (h' : a' ∣ b' ^ 2 - f) (ha : IsCoprime a f) (ha' : IsCoprime a' f)
    (hab : mumfordClass f a b = mumfordClass f a' b') :
    IsSquare (mumfordValue f a * mumfordValue f a') := by
  obtain ⟨p, q, hpq⟩ := exists_associated_sq_sub_mul_sq_of_mumfordClass_eq f h h' hab
  rw [← mumfordValue_mul f ha ha', ← mumfordValue_eq_of_associated f hpq]
  exact isSquare_mumfordValue_sq_sub_mul_sq f Fact.out
    (hpq.isCoprime_iff_left.mpr (ha.mul_left ha'))

end ChabautyColeman

end

/-! ### The map, by a choice of representatives -/

public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K] (f : K[X]) [Fact (Odd f.natDegree)] [NeZero (2 : K)]
  [Fact (Squarefree f)]

-- The map `ChabautyColeman.HypJac.descentMap` before it is known to be a homomorphism: the class
-- of the value of the first polynomial of a chosen representative prime to `f`.
private noncomputable def descentMapFun (x : HypJac K f) : Units.ModPow (AdjoinRoot f) 2 :=
  (isUnit_mumfordValue f Fact.out
    (x.exists_isCoprime_mumfordClass_eq f one_ne_zero).choose_spec.choose_spec.1).unit

private theorem descentMapFun_mumfordClass {a b : K[X]} (h : a ∣ b ^ 2 - f) (ha : IsCoprime a f)
    {u : (AdjoinRoot f)ˣ} (hu : (u : AdjoinRoot f) = mumfordValue f a) :
    descentMapFun f (mumfordClass f a b) = u := by
  obtain ⟨h₀, hc₀, he₀⟩ :=
    ((mumfordClass f a b).exists_isCoprime_mumfordClass_eq f one_ne_zero).choose_spec.choose_spec
  rw [descentMapFun, Units.ModPow.mk_eq_mk_iff_isSquare_mul, IsUnit.unit_spec, hu]
  exact isSquare_mumfordValue_mul_of_mumfordClass_eq f h₀ h hc₀.of_mul_right_left ha he₀

private theorem descentMapFun_mul (x y : HypJac K f) :
    descentMapFun f (x * y) = descentMapFun f x * descentMapFun f y := by
  obtain ⟨a, b, h, ha, rfl⟩ := x.exists_isCoprime_mumfordClass_eq f one_ne_zero
  rw [mul_one] at ha
  obtain ⟨a', b', h', ha', rfl⟩ :=
    y.exists_isCoprime_mumfordClass_eq f (ne_zero_of_dvd_ne_zero (sq_sub_ne_zero f b) h)
  have hc : IsCoprime a a' := ha'.of_mul_right_right.symm
  obtain ⟨B, hB, hB'⟩ := hc.exists_dvd_sub_and_dvd_sub b b'
  have hB₀ : a * a' ∣ B ^ 2 - f :=
    hc.mul_dvd ((dvd_sq_sub_iff_of_dvd_sub hB).mpr h) ((dvd_sq_sub_iff_of_dvd_sub hB').mpr h')
  have hu := isUnit_mumfordValue f Fact.out h
  have hu' := isUnit_mumfordValue f Fact.out h'
  rw [← mumfordClass_mul_of_dvd_sub f hB₀ hB hB', descentMapFun_mumfordClass f h ha hu.unit_spec,
    descentMapFun_mumfordClass f h' ha'.of_mul_right_left hu'.unit_spec,
    descentMapFun_mumfordClass f (u := hu.unit * hu'.unit) hB₀ (ha.mul_left ha'.of_mul_right_left)
      (by simp [mumfordValue_mul f ha ha'.of_mul_right_left])]
  rfl

/-- The **`x - T` map** `μ : J(K) → L^× / (L^×)^2` of 2-descent, `L = K[X] / (f)`, of [Sto17],
Section 5: the class of `ChabautyColeman.mumfordValue f a` for any Mumford representative `(a, b)`
with `a` prime to `f` (`ChabautyColeman.HypJac.descentMap_mumfordClass_of_isCoprime`). It is
defined by a choice of such a representative; it does not depend on the choice by
`ChabautyColeman.isSquare_mumfordValue_mul_of_mumfordClass_eq`. -/
noncomputable def HypJac.descentMap : HypJac K f →* Units.ModPow (AdjoinRoot f) 2 :=
  .mk' (descentMapFun f) (descentMapFun_mul f)

theorem HypJac.descentMap_mumfordClass_of_isCoprime {a b : K[X]} (h : a ∣ b ^ 2 - f)
    (ha : IsCoprime a f) {u : (AdjoinRoot f)ˣ} (hu : (u : AdjoinRoot f) = mumfordValue f a) :
    HypJac.descentMap f (mumfordClass f a b) = u :=
  descentMapFun_mumfordClass f h ha hu

/-- The **formula for the `x - T` map** of [Sto17], Section 5: the class of a Mumford pair `(a, b)`
maps to the class of `ChabautyColeman.mumfordValue f a`, also when `a` is not prime to `f`. The
moving lemma `Squarefree.exists_mul_eq_sub_sq_and_isCoprime` gives the representative
`(a'', -(b + k * a))` with `a * a'' = f - (b + k * a) ^ 2` and `a''` prime to `f`, and
`ChabautyColeman.isSquare_mumfordValue_mul_of_mul_eq_sub_sq` compares the values of `a` and
`a''`. -/
theorem HypJac.descentMap_mumfordClass {a b : K[X]} (h : a ∣ b ^ 2 - f) {u : (AdjoinRoot f)ˣ}
    (hu : (u : AdjoinRoot f) = mumfordValue f a) :
    HypJac.descentMap f (mumfordClass f a b) = u := by
  have hf : Squarefree f := Fact.out
  obtain ⟨k, a'', hmul, hcop⟩ := hf.exists_mul_eq_sub_sq_and_isCoprime
    (by simpa [← C_ofNat] using NeZero.ne (2 : K)) h hf.ne_zero
  have h'' : a'' ∣ (-(b + k * a)) ^ 2 - f := ⟨-a, by linear_combination hmul⟩
  have hu'' := isUnit_mumfordValue f hf h''
  rw [mumfordClass_eq_of_mul_eq_sub_sq f hmul,
    descentMap_mumfordClass_of_isCoprime f h'' hcop hu''.unit_spec,
    Units.ModPow.mk_eq_mk_iff_isSquare_mul, IsUnit.unit_spec, hu, mul_comm]
  exact isSquare_mumfordValue_mul_of_mul_eq_sub_sq f hf Fact.out hmul hcop

/-- The value of the `x - T` map at the class of `(a, 0)`, `f = a * e`, a point of order dividing
`2`: the class of `(-c) ^ deg a * lc(a)⁻¹ * (a - e)`, `c` the leading coefficient of `f`, a closed
form without the gcd. It differs from `ChabautyColeman.mumfordValue f a` by the square `lc(a) ^ 2`
in the components at the factors of `a`, and agrees with it for monic `a`. -/
theorem HypJac.descentMap_mumfordClass_zero_of_mul_eq {a e : K[X]} (h : a * e = f)
    {u : (AdjoinRoot f)ˣ} (hu : (u : AdjoinRoot f) = AdjoinRoot.mk f
      (C ((-f.leadingCoeff) ^ a.natDegree * a.leadingCoeff⁻¹) * (a - e))) :
    HypJac.descentMap f (mumfordClass f a 0) = u := by
  have hf : Squarefree f := Fact.out
  have h0 : a ∣ 0 ^ 2 - f := ⟨-e, by linear_combination h⟩
  have ha : a ≠ 0 := left_ne_zero_of_mul (h.symm ▸ hf.ne_zero)
  have hc : C a.leadingCoeff⁻¹ * C a.leadingCoeff = 1 := by
    rw [← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr ha), C_1]
  rw [descentMap_mumfordClass f h0 (isUnit_mumfordValue f hf h0).unit_spec,
    Units.ModPow.mk_eq_mk_iff_isSquare_mul, IsUnit.unit_spec, hu,
    mumfordValue_eq_of_mul_eq f (monic_mul_leadingCoeff_inv ha) (a₁ := C a.leadingCoeff)
      (f₁ := C a.leadingCoeff * e) (by linear_combination a * hc)
      (by linear_combination a * e * hc + h)
      (IsUnit.of_mul_eq_one_right _ hc).isRelPrime_left.isCoprime]
  set k := (-f.leadingCoeff) ^ a.natDegree * a.leadingCoeff⁻¹
  refine ⟨AdjoinRoot.mk f (C k * (a + C a.leadingCoeff * e)), ?_⟩
  rw [← map_mul, ← map_mul, AdjoinRoot.mk_eq_mk]
  exact ⟨-(C k * (1 + C a.leadingCoeff)) ^ 2,
    by linear_combination -(C k * (1 + C a.leadingCoeff)) ^ 2 * h⟩

-- The component at a root `r` of `f` of the value of the `x - T` map at the point `(a, 0)`, in
-- terms of the cofactor `e` of `X - C a`.
private theorem HypJac.map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero {a r : K} {e : K[X]}
    (he : (X - C a) * e = f) (hr : f.IsRoot r) {u : Kˣ}
    (hu : (u : K) = f.leadingCoeff * (a - r + e.eval r)) :
    Units.ModPow.map (AdjoinRoot.liftAlgHom f (Algebra.ofId K K) r (by simpa using hr)) 2
      (descentMap f (mumfordClass f (X - C a) 0)) = (u : Units.ModPow K 2) := by
  have h0 : X - C a ∣ 0 ^ 2 - f := ⟨-e, by linear_combination he⟩
  rw [descentMap_mumfordClass f h0 (isUnit_mumfordValue f Fact.out h0).unit_spec,
    Units.ModPow.map_mk]
  congr 1
  ext
  simp [mumfordValue_eq_of_mul_eq f (monic_X_sub_C a) (mul_one _) he isCoprime_one_left, hu]
  ring

/-- The component at a root `r` of `f` of the value of the `x - T` map at the point `(a, 0)`, for a
second root `a ≠ r` of `f`: the class of `lc(f) * (a - r)`. This is the component of
`ChabautyColeman.HypJac.descentMap_mumfordClass_zero_of_mul_eq` for the divisor `X - C a`. -/
theorem HypJac.map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero_of_ne {a r : K}
    (ha : f.IsRoot a) (hr : f.IsRoot r) (hne : r ≠ a) {u : Kˣ}
    (hu : (u : K) = f.leadingCoeff * (a - r)) :
    Units.ModPow.map (AdjoinRoot.liftAlgHom f (Algebra.ofId K K) r (by simpa using hr)) 2
      (descentMap f (mumfordClass f (X - C a) 0)) = (u : Units.ModPow K 2) := by
  have he := mul_divByMonic_eq_iff_isRoot.mpr ha
  refine map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero f he hr ?_
  have h := congr(eval r $he)
  rw [eval_mul, hr.eq_zero, eval_sub, eval_X, eval_C] at h
  rw [hu, (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne), add_zero]

/-- The component at a root `a` of `f` of the value of the `x - T` map at the point `(a, 0)`: the
class of `lc(f) * f'(a)`. This is the component of
`ChabautyColeman.HypJac.descentMap_mumfordClass_zero_of_mul_eq` for the divisor `X - C a`, where the
cofactor takes the value `f'(a)`. -/
theorem HypJac.map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero_self {a : K}
    (ha : f.IsRoot a) {u : Kˣ} (hu : (u : K) = f.leadingCoeff * f.derivative.eval a) :
    Units.ModPow.map (AdjoinRoot.liftAlgHom f (Algebra.ofId K K) a (by simpa using ha)) 2
      (descentMap f (mumfordClass f (X - C a) 0)) = (u : Units.ModPow K 2) := by
  obtain ⟨e, he⟩ := dvd_iff_isRoot.mpr ha
  refine map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero f he.symm ha ?_
  rw [hu, he]
  simp

/-- The value of the `x - T` map at a point `(x₀, y₀)` with `f(x₀) ≠ 0`: the class of
`lc(f) * (x₀ - θ)`, `θ` the root of `L = K[X] / (f)` (`ChabautyColeman.mumfordValue_of_isCoprime`
for `a = X - C x₀`). -/
theorem HypJac.descentMap_mumfordClass_X_sub_C {x₀ y₀ : K} (hy : y₀ ^ 2 = f.eval x₀)
    (h0 : f.eval x₀ ≠ 0) {u : (AdjoinRoot f)ˣ}
    (hu : (u : AdjoinRoot f) =
      AdjoinRoot.of f f.leadingCoeff * (AdjoinRoot.of f x₀ - AdjoinRoot.root f)) :
    descentMap f (mumfordClass f (X - C x₀) (C y₀)) = u := by
  refine descentMap_mumfordClass f (dvd_iff_isRoot.mpr (by simp [hy])) ?_
  rw [hu, mumfordValue_of_isCoprime f ((irreducible_X_sub_C x₀).coprime_iff_not_dvd.mpr
    (by rwa [dvd_iff_isRoot]))]
  simp [AdjoinRoot.mk_X]
  ring

/-- **The norm condition**: `μ(x)` lies in the kernel of the map `L^× / (L^×)^2 → K^× / (K^×)^2`
induced by the norm. For a representative `(a, b)` of `x` with `a` prime to `f`
(`ChabautyColeman.HypJac.exists_isCoprime_mumfordClass_eq`), the norm of
`ChabautyColeman.mumfordValue f a` is a square by `ChabautyColeman.isSquare_norm_mumfordValue`. -/
theorem HypJac.descentMap_mem_ker_norm (x : HypJac K f) :
    descentMap f x ∈ (Units.ModPow.map (Algebra.norm K) 2).ker := by
  obtain ⟨a, b, h, ha, rfl⟩ := x.exists_isCoprime_mumfordClass_eq f one_ne_zero
  have hu := isUnit_mumfordValue f Fact.out h
  rw [MonoidHom.mem_ker, descentMap_mumfordClass f h hu.unit_spec, Units.ModPow.map_unit,
    Units.ModPow.mk_eq_one_iff_isSquare, IsUnit.unit_spec]
  exact isSquare_norm_mumfordValue f Fact.out h (by simpa using ha)

section BaseChange

variable {K' : Type*} [Field K'] [Algebra K K'] [NeZero (2 : K')]
  [Fact (Squarefree (f.map (algebraMap K K')))]

/-- **Base change** of the `x - T` map along a field extension `K ⊆ K'`: the image of `μ(x)` under
the map `L → L' = K'[X] / (f)` (Mathlib's `AdjoinRoot.map`) is `μ'` of the image of `x` in
`J(K')`. A Mumford representative `(a, b)` of `x` over `K` maps to one over `K'`
(`ChabautyColeman.HypJac.map_mumfordClass`), and the value of `a` maps to the value of its image
(`ChabautyColeman.map_mumfordValue`). -/
theorem HypJac.map_descentMap (x : HypJac K f) :
    Units.ModPow.map (AdjoinRoot.map (algebraMap K K') f (f.map (algebraMap K K')) dvd_rfl) 2
        (descentMap f x) =
      descentMap (f.map (algebraMap K K')) (HypJac.map f x) := by
  obtain ⟨a, b, h, -, rfl⟩ := x.exists_isCoprime_mumfordClass_eq f one_ne_zero
  have hu := isUnit_mumfordValue f Fact.out h
  rw [descentMap_mumfordClass f h hu.unit_spec, Units.ModPow.map_unit, HypJac.map_mumfordClass]
  exact (descentMap_mumfordClass _ (by simpa using Polynomial.map_dvd (algebraMap K K') h)
    (by simp [map_mumfordValue])).symm

/-- **Base change** of the `x - T` map, `ChabautyColeman.HypJac.map_descentMap`, as the
commutative square of homomorphisms that the key theorem takes. -/
theorem HypJac.map_comp_descentMap :
    (Units.ModPow.map (AdjoinRoot.map (algebraMap K K') f (f.map (algebraMap K K')) dvd_rfl)
        2).comp (descentMap f) =
      (descentMap (f.map (algebraMap K K'))).comp (HypJac.map f) :=
  MonoidHom.ext fun x ↦ by simp only [MonoidHom.comp_apply, map_descentMap]

end BaseChange

end ChabautyColeman

end
