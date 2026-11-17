/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

-- Beyond the sibling, for the proof of `QuadraticAlgebra.liftRingHom` only: the tactic
-- `linear_combination`.
import Mathlib.Tactic.LinearCombination

/-!
# The universal property of a quadratic algebra for ring homomorphisms

## Main definitions

* `QuadraticAlgebra.liftRingHom`: the ring homomorphism `QuadraticAlgebra R a b →+* S` induced by
  a ring homomorphism `φ : R →+* S` and a root `s` of `s ^ 2 = φ a + φ b * s`. Unlike
  `QuadraticAlgebra.lift`, the base map is arbitrary (the target need not be an `R`-algebra).

## Main statements

* `QuadraticAlgebra.liftRingHom_omega`, `QuadraticAlgebra.liftRingHom_comp_algebraMap`: the
  induced map sends `ω` to `s` and restricts to `φ`.

The universal property maps the function field of a hyperelliptic curve into a series field by
choosing a square root of `f`; the expansion charts of the function field
(`HyperellipticCurves.Archive.DiskExpand`, `HyperellipticCurves.Archive.InftyExpand`,
`HyperellipticCurves.Archive.InftyTransport`, `HyperellipticCurves.Archive.WeierstrassTransport`)
are built from it. The main development expands curve functions disk by disk over `Frac(K⟦z⟧)`
instead.

Auxiliary material for the Archive of the formalization of the Chabauty–Coleman bound for
hyperelliptic curves (the main theorems do not depend on it); upstreaming candidates for
Mathlib.
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

end QuadraticAlgebra

end
