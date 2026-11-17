/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Descent.Map
public import HyperellipticCurves.Descent.Selmer

import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot

/-!
# The image of the descent map

Let `K` be a perfect field, the fraction field of a Dedekind domain `R`, let `f` be squarefree of
odd degree over `K`, and let `S` be a set of primes of `R` outside which `f` has separable
reduction (`Polynomial.HasSeparableReduction`). Then the descent map
`μ : J(K) → (K[X] ⧸ (f))ˣ / squares` takes values in `A(S, 2)`. A point is the class of `(a, b)`
with `a` prime to `f`, and the component of `μ` of it in a field factor `L_p` is
`(-c) ^ deg a * lc(a)⁻¹ * a(θ_p)`, which lies in the Selmer group of `L_p` by the point lemma for
Mumford polynomials.

## Main statements

* `ChabautyColeman.algHom_mumfordValue_mem_selmerGroupAbove`: the image of
  `ChabautyColeman.mumfordValue f a` in a field `L` lies in the Selmer group of `L`.
* `ChabautyColeman.HypJac.range_descentMap_le_selmerGroup`: `μ(J(K)) ⊆ A(S, 2)`.
* `ChabautyColeman.HypJac.mk_mem_range_descentMap_of_isSquare`: the class of `x₀ - θ` lies in the
  image of `μ` if `f(x₀)` is a square.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5
-/

@[expose] public section

open Polynomial IsDedekindDomain

namespace ChabautyColeman

section Component

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Algebra.IsIntegral R B] [Module.IsTorsionFree R B] {L : Type*} [Field L] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L]
  [PerfectField L]

/-- The image of the value `ChabautyColeman.mumfordValue f a` of a Mumford polynomial `a` prime to
`f` under a homomorphism `φ` from `K[X] ⧸ (f)` to `L` lies in the Selmer group of `L` relative to
the primes above `S`. With `θ = φ T` and `c` the leading coefficient of `f`, the image is
`(-c) ^ deg a * lc(a)⁻¹ * a(θ)`; the class of `lc(a)⁻¹ * a(θ)` lies in it by
`IsDedekindDomain.mem_selmerGroupAbove_of_dvd_sq_sub`, and that of `(-c) ^ deg a` as `c` is a unit
outside `S`. -/
theorem algHom_mumfordValue_mem_selmerGroupAbove {f : K[X]} (hodd : Odd f.natDegree)
    {S : Set (HeightOneSpectrum R)} (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K))
    (φ : AdjoinRoot f →ₐ[K] L) {a b : K[X]} (h : a ∣ b ^ 2 - f) (ha : IsCoprime a f) {u : Lˣ}
    (hu : (u : L) = φ (mumfordValue f a)) :
    (u : Units.ModPow L 2) ∈ selmerGroupAbove R B L S 2 := by
  have hc : algebraMap K L ((-f.leadingCoeff) ^ a.natDegree) ≠ 0 := by
    simp [ne_zero_of_natDegree_gt hodd.pos]
  rw [← mul_inv_cancel_left (Units.mk0 _ hc) u]
  refine mul_mem (mem_selmerGroupAbove_of_valuation_eq_one
      (fun v hv ↦ by simp [(hS v hv).leadingCoeff_eq_one]) rfl)
    (mem_selmerGroupAbove_of_dvd_sq_sub hodd hS
      (AdjoinRoot.aeval_algHom_eq_zero f φ) (b := b.map (algebraMap K L))
      (by simpa using Polynomial.map_dvd (algebraMap K L) h) ((isCoprime_map _).mpr ha) ?_)
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, hu, mumfordValue_of_isCoprime f ha,
    ← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, map_mul, aeval_C, leadingCoeff_map,
    eval_map_algebraMap, map_mul, map_inv₀, mul_assoc, inv_mul_cancel_left₀ hc]

end Component

section SelmerGroup

variable {K : Type*} [Field K] (f : K[X]) [Fact (Odd f.natDegree)] [NeZero (2 : K)]
  [Fact (Squarefree f)] [PerfectField K] {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Algebra R K] [IsFractionRing R K]

/-- **The image of the `x - T` map** ([Sto17], Section 5): if `f` has separable reduction at the
primes of `R` outside `S`, then `μ(J(K)) ⊆ A(S, 2)`. A point is the class of `(a, b)` with `a`
prime to `f` (`ChabautyColeman.HypJac.exists_isCoprime_mumfordClass_eq`), `μ` maps it to the class
of `ChabautyColeman.mumfordValue f a`, and its component in each field factor lies in the Selmer
group of the factor by `ChabautyColeman.algHom_mumfordValue_mem_selmerGroupAbove`. -/
theorem HypJac.range_descentMap_le_selmerGroup {S : Set (HeightOneSpectrum R)}
    (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K)) :
    (descentMap f).range ≤ AdjoinRoot.selmerGroup Fact.out S 2 := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, b, h, ha, rfl⟩ := x.exists_isCoprime_mumfordClass_eq f one_ne_zero
  rw [mul_one] at ha
  have hu := isUnit_mumfordValue f Fact.out h
  rw [descentMap_mumfordClass_of_isCoprime f h ha hu.unit_spec]
  refine (AdjoinRoot.mem_selmerGroup_iff ..).mpr fun p ↦ ?_
  rw [AdjoinRoot.modPowEquivPiFactors_mk]
  exact algHom_mumfordValue_mem_selmerGroupAbove Fact.out hS
    ((Pi.evalAlgHom K _ p).comp (AdjoinRoot.equivPiFactors Fact.out).toAlgHom) h ha rfl

end SelmerGroup

section Points

variable {K : Type*} [Field K] {f : K[X]} [Fact (Odd f.natDegree)] [NeZero (2 : K)]
  [Fact (Squarefree f)]

/-- **Points with a given `x`-coordinate** in the image of the `x - T` map: for monic `f` and a
unit `u = x₀ - θ` of `K[X] ⧸ (f)` with `f(x₀)` a square, the class of `u` is the value of the
`x - T` map at a point `(x₀, y₀)` (`ChabautyColeman.HypJac.descentMap_mumfordClass_X_sub_C`);
`f(x₀) ≠ 0` as `u` is a unit (`AdjoinRoot.isUnit_of_sub_root_iff`). -/
theorem HypJac.mk_mem_range_descentMap_of_isSquare (hf : f.Monic) {x₀ : K}
    (hsq : IsSquare (f.eval x₀)) {u : (AdjoinRoot f)ˣ}
    (hu : (u : AdjoinRoot f) = AdjoinRoot.of f x₀ - AdjoinRoot.root f) :
    (u : Units.ModPow (AdjoinRoot f) 2) ∈ (descentMap f).range := by
  obtain ⟨y, hy⟩ := hsq
  exact ⟨_, descentMap_mumfordClass_X_sub_C f (y₀ := y) (by rw [hy, sq])
    (AdjoinRoot.isUnit_of_sub_root_iff.mp (hu ▸ u.isUnit))
    (by rw [hu, hf.leadingCoeff, map_one, one_mul])⟩

end Points

end ChabautyColeman
