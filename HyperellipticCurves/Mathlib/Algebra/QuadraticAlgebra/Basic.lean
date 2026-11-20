/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

-- Beyond the sibling, for the proofs only: the simp lemmas `QuadraticAlgebra.re_algebraMap` and
-- `QuadraticAlgebra.im_algebraMap` (the mirror of `Mathlib.Algebra.QuadraticAlgebra.Defs`).
import HyperellipticCurves.Mathlib.Algebra.QuadraticAlgebra.Defs

/-!
# Conjugation and functoriality of quadratic algebras

## Main definitions

* `QuadraticAlgebra.mapRingHomTo`: functoriality in the coefficient ring with prescribed target
  coefficients. Unlike `QuadraticAlgebra.mapRingHom`, whose target is
  `QuadraticAlgebra R' (φ a) (φ b)`, the identities `φ a = a'`, `φ b = b'` are hypotheses, so the
  map lands in a type indexed by given data without a cast.

## Main statements

* `QuadraticAlgebra.star_algebraMap`: conjugation fixes the image of the base.
* `QuadraticAlgebra.starAlgEquiv_symm`: Mathlib's `QuadraticAlgebra.starAlgEquiv` is an involution.
* `QuadraticAlgebra.omega_sq`, `QuadraticAlgebra.star_omega`: `ω ^ 2 = a + b • ω`, and
  conjugation sends `ω` to `b - ω`.
* `QuadraticAlgebra.mapRingHomTo_injective`: the induced map is injective when the coefficient
  map is.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R} {S : Type*} [CommSemiring S] [Algebra S R]

@[simp]
theorem star_algebraMap (s : S) :
    star (algebraMap S (QuadraticAlgebra R a b) s) = algebraMap S _ s := by
  ext <;> simp [re_star, im_star]

@[simp]
theorem starAlgEquiv_symm : (starAlgEquiv (R := R) (a := a) (b := b)).symm = starAlgEquiv := rfl

/-- The defining equation of the generator: `ω² = a + b·ω`. -/
theorem omega_sq : (ω : QuadraticAlgebra R a b) ^ 2 = algebraMap R _ a + b • ω := by
  rw [sq, omega_mul_omega_eq_add, Algebra.algebraMap_eq_smul_one]

/-- Conjugation sends `ω` to the other root `b - ω` of the defining equation. -/
@[simp]
theorem star_omega : star (ω : QuadraticAlgebra R a b) = algebraMap R _ b - ω := by
  ext <;> simp [omega]

section map

variable {R' : Type*} [CommRing R'] {a' b' : R'}

/-- Functoriality of `QuadraticAlgebra` in the coefficient ring: a ring homomorphism
mapping the defining coefficients to the defining coefficients induces a ring
homomorphism, componentwise. Unlike `QuadraticAlgebra.mapRingHom`, whose target is
`QuadraticAlgebra R' (φ a) (φ b)`, the target coefficients `a'`, `b'` are prescribed and the
identities `φ a = a'`, `φ b = b'` are hypotheses, so the map lands in a type indexed by given data
(a polynomial `g` with `f.map φ = g`) without a cast. -/
def mapRingHomTo (φ : R →+* R') (ha : φ a = a') (hb : φ b = b') :
    QuadraticAlgebra R a b →+* QuadraticAlgebra R' a' b' where
  toFun z := ⟨φ z.re, φ z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp [← ha, ← hb]
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp]
theorem re_mapRingHomTo (φ : R →+* R') (ha : φ a = a') (hb : φ b = b')
    (z : QuadraticAlgebra R a b) : (mapRingHomTo φ ha hb z).re = φ z.re := rfl

@[simp]
theorem im_mapRingHomTo (φ : R →+* R') (ha : φ a = a') (hb : φ b = b')
    (z : QuadraticAlgebra R a b) : (mapRingHomTo φ ha hb z).im = φ z.im := rfl

/-- The induced map is injective as soon as the coefficient map is: it acts componentwise. -/
theorem mapRingHomTo_injective {φ : R →+* R'} (hφ : Function.Injective φ) (ha : φ a = a')
    (hb : φ b = b') : Function.Injective (mapRingHomTo φ ha hb) := by
  subst ha hb
  exact mapRingHom_injective φ a b hφ

end map

end QuadraticAlgebra

end
