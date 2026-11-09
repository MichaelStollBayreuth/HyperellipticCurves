/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

import Mathlib.Tactic.LinearCombination

/-!
# The universal property of a quadratic algebra, and componentwise sums

Two complements to `QuadraticAlgebra` whose only clients lie in the Archive: the
ring-homomorphism form of the universal property (`QuadraticAlgebra.liftRingHom`), which
maps the function field of a hyperelliptic curve into a series field by choosing a square
root of `f`, and the real and imaginary parts of a finite sum.

The universal property is what the expansion charts of the function field
(`HyperellipticCurves.Archive.DiskExpand`, `HyperellipticCurves.Archive.InftyExpand`,
`HyperellipticCurves.Archive.InftyTransport`, `HyperellipticCurves.Archive.WeierstrassTransport`)
are built from; the main development expands curve functions disk by disk over `Frac(K⟦z⟧)`
instead. The component sums serve the place-by-place valuation bounds
(`HyperellipticCurves.Archive.OmegaRegular`).
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

section lift

variable {S : Type*} [CommRing S]

/-- **Universal property of `QuadraticAlgebra R a b`, ring-homomorphism version**: a ring
homomorphism `φ : R →+* S` together with a root `s` of the defining equation
`s² = φ a + φ b · s` induces a ring homomorphism `QuadraticAlgebra R a b →+* S` sending
`⟨x, y⟩ = x + y·ω` to `φ x + φ y · s`. Unlike `QuadraticAlgebra.lift`, the base map `φ` is
arbitrary (the target need not be an `R`-algebra). -/
def liftRingHom (φ : R →+* S) (s : S) (hs : s ^ 2 = φ a + φ b * s) :
    QuadraticAlgebra R a b →+* S where
  toFun z := φ z.re + φ z.im * s
  map_one' := by simp
  map_mul' z w := by
    simp only [re_mul, im_mul, map_add, map_mul]
    linear_combination -(φ z.im * φ w.im) * hs
  map_zero' := by simp
  map_add' z w := by
    simp only [re_add, im_add, map_add]
    ring

@[simp]
theorem liftRingHom_apply (φ : R →+* S) (s : S) (hs : s ^ 2 = φ a + φ b * s)
    (z : QuadraticAlgebra R a b) : liftRingHom φ s hs z = φ z.re + φ z.im * s := rfl

theorem liftRingHom_omega (φ : R →+* S) (s : S) (hs : s ^ 2 = φ a + φ b * s) :
    liftRingHom φ s hs ω = s := by
  simp [omega]

theorem liftRingHom_comp_algebraMap (φ : R →+* S) (s : S) (hs : s ^ 2 = φ a + φ b * s) :
    (liftRingHom φ s hs).comp (algebraMap R (QuadraticAlgebra R a b)) = φ := by
  ext r
  simp

end lift

/-- The real part of a finite sum in a quadratic algebra. -/
theorem re_sum {R : Type*} [CommRing R] {a b : R} {ι : Type*}
    (s : Finset ι) (g : ι → QuadraticAlgebra R a b) :
    (∑ j ∈ s, g j).re = ∑ j ∈ s, (g j).re :=
  map_sum (AddMonoidHom.mk' QuadraticAlgebra.re fun _ _ ↦ rfl) g s

/-- The imaginary part of a finite sum in a quadratic algebra. -/
theorem im_sum {R : Type*} [CommRing R] {a b : R} {ι : Type*}
    (s : Finset ι) (g : ι → QuadraticAlgebra R a b) :
    (∑ j ∈ s, g j).im = ∑ j ∈ s, (g j).im :=
  map_sum (AddMonoidHom.mk' QuadraticAlgebra.im fun _ _ ↦ rfl) g s

end QuadraticAlgebra

end
