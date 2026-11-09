/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.MumfordReduction
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

import HyperellipticCurves.Archive.ForMathlib.Squarefree

/-!
# The conjugate ideal and the norm: ι inverts the Jacobian

The main theorems do not depend on this file: the main development inverts classes only of
*Mumford* ideals, where the Mumford norm identity `ChabautyColeman.mumfordIdeal_mul_map_star`
gives the inversion directly (`ChabautyColeman.classGroup_mk0_mumfordIdeal_map_star` in
`HyperellipticCurves.Curve.MumfordReduction`). The general identity `𝔞·ι(𝔞) = (Nm 𝔞)` is clean
Mathlib-bound API (restated for a general quadratic Dedekind extension it would be a natural
PR).

For every ideal `𝔞` of the coordinate ring `A_K` we prove
`𝔞 · ι(𝔞) = (Nm 𝔞) A_K` (`ChabautyColeman.mul_map_star_eq_map_relNorm`), where
`Nm 𝔞 = Ideal.relNorm K[X] 𝔞` and `ι` is the `star` involution. Consequently the
involution inverts ideal classes (`ChabautyColeman.classGroup_mk0_map_star`),
extending `ChabautyColeman.aj_inv` from point classes to all of `J(K)`.

The proof avoids factorization into primes entirely: since `K[x]` is a PID,
`Nm 𝔞 = (n₀)` is principal, and for `t = a·ι(b)` with `a, b ∈ 𝔞` one reads off
`n₀ ∣ 2·re t` from the trace `N(a+b) - N(a) - N(b)` and `n₀² ∣ (re t)² - f·(im t)²`
from the norm `N(a)·N(b)`; squarefreeness of `f` then gives `n₀ ∣ im t` by
`Squarefree.dvd_of_sq_dvd_mul_sq`.

Blueprint node: `lem:iota-norm`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

open QuadraticAlgebra Ideal

variable {K : Type*} [Field K] (f : K[X])

variable [Fact (Odd f.natDegree)]

variable [NeZero (2 : K)] [Fact (Squarefree f)]

lemma algebraMap_intNorm_eq (z : HypRing K f) :
    algebraMap K[X] (HypRing K f) (Algebra.intNorm K[X] (HypRing K f) z) = z * star z := by
  rw [Algebra.intNorm_eq_norm, ← HypRing.mul_star_eq_norm]

-- The trace of `a·ι(b)` on `K[x]`: `N(a+b) - N(a) - N(b)`.
private lemma two_mul_re_eq (a b : HypRing K f) :
    2 * (a * star b).re = Algebra.intNorm K[X] (HypRing K f) (a + b)
      - Algebra.intNorm K[X] (HypRing K f) a - Algebra.intNorm K[X] (HypRing K f) b := by
  have hinj : Function.Injective (algebraMap K[X] (HypRing K f)) :=
    QuadraticAlgebra.algebraMap_injective
  apply hinj
  have h1 : a * star b + star (a * star b)
      = algebraMap K[X] (HypRing K f) (2 * (a * star b).re) := by
    simpa [QuadraticAlgebra.trace_def] using
      (QuadraticAlgebra.algebraMap_trace_eq_add_star (a * star b)).symm
  rw [map_sub, map_sub, algebraMap_intNorm_eq, algebraMap_intNorm_eq, algebraMap_intNorm_eq,
    ← h1, star_mul, star_star, star_add]
  ring

-- The norm of `a·ι(b)`: `N(a)·N(b)`.
private lemma re_sq_sub_im_sq (a b : HypRing K f) :
    (a * star b).re ^ 2 - f * (a * star b).im ^ 2
      = Algebra.intNorm K[X] (HypRing K f) a * Algebra.intNorm K[X] (HypRing K f) b := by
  have hinj : Function.Injective (algebraMap K[X] (HypRing K f)) :=
    QuadraticAlgebra.algebraMap_injective
  apply hinj
  rw [map_mul, algebraMap_intNorm_eq, algebraMap_intNorm_eq, ← HypRing.norm_eq,
    ← HypRing.mul_star_eq_norm, star_mul, star_star]
  ring

-- the key divisibility: products `a · ι(b)` with `a, b ∈ I` lie in `(Nm I) · A_K`
private lemma mul_star_mem {I : Ideal (HypRing K f)} {a b : HypRing K f}
    (ha : a ∈ I) (hb : b ∈ I) :
    a * star b ∈ (relNorm K[X] I).map (algebraMap K[X] (HypRing K f)) := by
  set t := a * star b with hts
  set n₀ := Submodule.IsPrincipal.generator (relNorm K[X] I) with hn₀
  have hgen (z : HypRing K f) (hz : z ∈ I) : n₀ ∣ Algebra.intNorm K[X] (HypRing K f) z := by
    have hmem : Algebra.intNorm K[X] (HypRing K f) z ∈ relNorm K[X] I := by
      rw [← spanNorm_eq]
      exact intNorm_mem_spanNorm K[X] hz
    exact (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp hmem
  -- the trace `N(a+b) - N(a) - N(b)` and norm `N(a)·N(b)` of `t = a·ι(b)`
  have htr := two_mul_re_eq f a b
  have hnm := re_sq_sub_im_sq f a b
  rw [← hts] at htr hnm
  have h2u : IsUnit (2 : K[X]) := by
    have h : (2 : K[X]) = C 2 := by rw [map_ofNat]
    rw [h, Polynomial.isUnit_C]
    exact (two_ne_zero (α := K)).isUnit
  have hre : n₀ ∣ t.re := by
    have h := dvd_sub (dvd_sub (hgen _ (I.add_mem ha hb)) (hgen _ ha)) (hgen _ hb)
    rw [← htr] at h
    exact h2u.dvd_mul_left.mp h
  have him : n₀ ∣ t.im := by
    have h : n₀ ^ 2 ∣ f * t.im ^ 2 := by
      have h1 : n₀ ^ 2 ∣ t.re ^ 2 - f * t.im ^ 2 := by
        rw [hnm, sq]
        exact mul_dvd_mul (hgen _ ha) (hgen _ hb)
      have h2 : n₀ ^ 2 ∣ t.re ^ 2 := pow_dvd_pow_of_dvd hre 2
      simpa using dvd_sub h2 h1
    exact (Fact.out : Squarefree f).dvd_of_sq_dvd_mul_sq h
  obtain ⟨r, hr⟩ := hre
  obtain ⟨s, hs⟩ := him
  rw [← span_singleton_generator (relNorm K[X] I), Ideal.map_span, Set.image_singleton]
  exact mem_span_singleton.mpr ⟨⟨r, s⟩, by ext <;> simp [hr, hs, ← hn₀]⟩

/-- For every ideal of `A_K`: `𝔞 · ι(𝔞) = (Nm 𝔞) A_K`. -/
theorem mul_map_star_eq_map_relNorm (I : Ideal (HypRing K f)) :
    I * I.map (starRingEnd (HypRing K f))
      = (relNorm K[X] I).map (algebraMap K[X] (HypRing K f)) := by
  refine le_antisymm (Ideal.mul_le.mpr fun a ha b' hb' ↦ ?_) ?_
  · obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (star_involutive.surjective)).mp hb'
    exact mul_star_mem f ha hb
  · rw [relNorm_apply, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [algebraMap_intNorm_eq]
    exact Ideal.mul_mem_mul ha (Ideal.mem_map_of_mem _ ha)

open nonZeroDivisors in
/-- The involution inverts ideal classes: `[ι(𝔞)] = [𝔞]⁻¹` in `J(K)`. -/
theorem classGroup_mk0_map_star {I : Ideal (HypRing K f)} (hI : I ∈ (Ideal (HypRing K f))⁰) :
    ClassGroup.mk0 ⟨I.map (starRingEnd (HypRing K f)), map_star_mem_nonZeroDivisors f hI⟩
      = (ClassGroup.mk0 ⟨I, hI⟩)⁻¹ := by
  set n₀ := Submodule.IsPrincipal.generator (relNorm K[X] I) with hn₀
  have hne : n₀ ≠ 0 := by
    rw [hn₀, ne_eq, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero, relNorm_eq_bot_iff]
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submodule.zero_eq_bot] at hI
    exact hI
  refine ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨algebraMap K[X] _ n₀,
    (map_ne_zero_iff _ QuadraticAlgebra.algebraMap_injective).mpr hne, ?_⟩
  change I.map (starRingEnd (HypRing K f)) * I = _
  rw [mul_comm, mul_map_star_eq_map_relNorm, ← span_singleton_generator (relNorm K[X] I),
    Ideal.map_span, Set.image_singleton, ← hn₀]

end ChabautyColeman

end
