/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Defs

/-!
# Components of elements of a quadratic algebra

## Main statements

* `QuadraticAlgebra.eq_zero_iff`, `QuadraticAlgebra.mk_eq_zero`,
  `QuadraticAlgebra.not_re_eq_zero_and_im_eq_zero`: an element is zero exactly when both
  components are.
* `QuadraticAlgebra.eq_algebraMap_re`: an element without imaginary part is the image of its real
  part.
* `QuadraticAlgebra.re_algebraMap`, `QuadraticAlgebra.im_algebraMap`: the components of
  `algebraMap S (QuadraticAlgebra R a b) s` for any base `S` of `R`.
* The instance `FaithfulSMul R (QuadraticAlgebra R a b)`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R} {S : Type*} [CommSemiring S] [Algebra S R]

instance : FaithfulSMul R (QuadraticAlgebra R a b) :=
  (faithfulSMul_iff_algebraMap_injective R _).mpr algebraMap_injective

theorem eq_zero_iff {z : QuadraticAlgebra R a b} : z = 0 ↔ z.re = 0 ∧ z.im = 0 := by
  simp [QuadraticAlgebra.ext_iff]

@[simp]
theorem mk_eq_zero {p q : R} : (⟨p, q⟩ : QuadraticAlgebra R a b) = 0 ↔ p = 0 ∧ q = 0 :=
  eq_zero_iff

/-- A nonzero element has a nonzero component. -/
theorem not_re_eq_zero_and_im_eq_zero {z : QuadraticAlgebra R a b} (hz : z ≠ 0) :
    ¬(z.re = 0 ∧ z.im = 0) := fun h ↦ hz (eq_zero_iff.mpr h)

/-- An element without imaginary part is the image of its real part. -/
theorem eq_algebraMap_re {z : QuadraticAlgebra R a b} (him : z.im = 0) :
    z = algebraMap R (QuadraticAlgebra R a b) z.re := by
  ext
  · simp
  · simp [him]

@[simp]
theorem re_algebraMap (s : S) :
    (algebraMap S (QuadraticAlgebra R a b) s).re = algebraMap S R s := rfl

@[simp]
theorem im_algebraMap (s : S) : (algebraMap S (QuadraticAlgebra R a b) s).im = 0 := rfl

end QuadraticAlgebra

end
