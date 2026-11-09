/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.HypRing
public import HyperellipticCurves.Specialization.Content

/-!
# Content normalization of abstract functions on the hyperelliptic curve

The main theorems do not depend on this file: generators arrive in the main development as
explicit polynomial pairs `(P, Q)`, so it uses only the pair-level content scalings of
`HyperellipticCurves.Specialization.Content`, not the function-level primitive generator
(blueprint `lem:content`) with its common-denominator clearing.

Given a valuation `v : K → ℤᵐ⁰`, every nonzero `h : HypField K f` has a `Kˣ`-multiple `c • h`
with a *primitive presentation*: `(algebraMap D) • (c • h) = ⟨algebraMap P, algebraMap Q⟩` where
`D` is a primitive common denominator (`contentVal v D = 1`) and `(P, Q)` is a jointly primitive
numerator (`contentVal v P ⊔ contentVal v Q = 1`). This is `exists_primitive_generator`
(`lem:content`).

The `𝓋`-content used to state primitivity is developed in
`HyperellipticCurves.Specialization.Content`. The scaling `c` is
a *constant* in `Kˣ` (it normalizes the `v`-adic content but not the `x`-poles, which are the
divisor of `h`). Uniqueness up to `Oˣ` is not needed downstream and is not formalized.
-/

@[expose] public section

open Polynomial QuadraticAlgebra

namespace ChabautyColeman

variable {K : Type*} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) {f : K[X]}

/-- `denom(r) · r = num(r)` in `RatFunc K` (after mapping to the function field). -/
theorem denom_mul_eq_num (r : RatFunc K) :
    algebraMap K[X] (RatFunc K) r.denom * r = algebraMap K[X] (RatFunc K) r.num := by
  have hd : algebraMap K[X] (RatFunc K) r.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (RatFunc.denom_ne_zero r)
  rw [mul_comm]
  exact ((div_eq_iff hd).mp (RatFunc.num_div_denom r)).symm

/-- A common denominator `D ≠ 0` clearing two rational functions to polynomials. -/
theorem exists_common_denom (r s : RatFunc K) :
    ∃ D : K[X], D ≠ 0 ∧ (∃ P : K[X], algebraMap K[X] (RatFunc K) D * r = algebraMap _ _ P) ∧
      (∃ Q : K[X], algebraMap K[X] (RatFunc K) D * s = algebraMap _ _ Q) :=
  ⟨r.denom * s.denom, mul_ne_zero (RatFunc.denom_ne_zero r) (RatFunc.denom_ne_zero s),
    ⟨s.denom * r.num, by rw [map_mul, mul_right_comm, denom_mul_eq_num, ← map_mul, mul_comm]⟩,
    ⟨r.denom * s.num, by rw [map_mul, mul_assoc, denom_mul_eq_num, ← map_mul]⟩⟩

/-- **Content normalization (`lem:content`).** Every nonzero `h : HypField K f` has a `Kˣ`-multiple
`c • h` with a primitive presentation `(algebraMap D) • (c • h) = ⟨algebraMap P, algebraMap Q⟩`:
a primitive common denominator `D` (`contentVal v D = 1`) and a jointly primitive numerator
`(P, Q)` (`contentVal v P ⊔ contentVal v Q = 1`). -/
theorem exists_primitive_generator (h : HypField K f) (hh : h ≠ 0) :
    ∃ (c : Kˣ) (P Q D : K[X]), D ≠ 0 ∧ contentVal v D = 1 ∧
      contentVal v P ⊔ contentVal v Q = 1 ∧
      algebraMap K[X] (RatFunc K) D • ((c : K) • h) =
        (⟨algebraMap K[X] (RatFunc K) P, algebraMap K[X] (RatFunc K) Q⟩ : HypField K f) := by
  obtain ⟨D₀, hD₀, ⟨P₁, hP₁⟩, ⟨Q₁, hQ₁⟩⟩ := exists_common_denom h.re h.im
  obtain ⟨d, hd⟩ := exists_primitive_smul v hD₀
  set D := C (d : K) * D₀ with hDdef
  have hDne : D ≠ 0 := mul_ne_zero (by simp [Units.ne_zero]) hD₀
  set P₀ := C (d : K) * P₁ with hP₀
  set Q₀ := C (d : K) * Q₁ with hQ₀
  have hDP : algebraMap K[X] (RatFunc K) D * h.re = algebraMap _ _ P₀ := by
    rw [hDdef, hP₀, map_mul, map_mul, mul_assoc, hP₁]
  have hDQ : algebraMap K[X] (RatFunc K) D * h.im = algebraMap _ _ Q₀ := by
    rw [hDdef, hQ₀, map_mul, map_mul, mul_assoc, hQ₁]
  have hDne' : algebraMap K[X] (RatFunc K) D ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDne
  have hPQ : ¬(P₀ = 0 ∧ Q₀ = 0) := by
    rintro ⟨hP0, hQ0⟩
    refine hh ?_
    ext
    · exact mul_left_cancel₀ hDne' (by rw [hDP, hP0]; simp)
    · exact mul_left_cancel₀ hDne' (by rw [hDQ, hQ0]; simp)
  obtain ⟨c, hc⟩ := exists_primitive_smul_pair v hPQ
  refine ⟨c, C (c : K) * P₀, C (c : K) * Q₀, D, hDne, hd, hc, ?_⟩
  have hC : algebraMap K (RatFunc K) (c : K) = algebraMap K[X] (RatFunc K) (C (c : K)) := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  ext
  · rw [re_smul, re_smul, smul_eq_mul, Algebra.smul_def, hC, mul_left_comm, hDP, ← map_mul]
  · rw [im_smul, im_smul, smul_eq_mul, Algebra.smul_def, hC, mul_left_comm, hDQ, ← map_mul]

end ChabautyColeman
