/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals under ring isomorphisms

A ring isomorphism induces a multiplicative isomorphism of the monoids of ideals. Mathlib has
`Ideal.map_of_equiv` and `Ideal.map_mul` but assembles neither into a bundled equivalence, which
is what the transport of a multiplicative invariant of ideals (multiplicity, the class group)
needs.

## Main definitions

* `Ideal.mapMulEquiv`: the multiplicative isomorphism `Ideal R ≃* Ideal S` induced by
  `R ≃+* S`.

## Main statements

* `Ideal.emultiplicity_map_ringEquiv`: `emultiplicity` of ideals is invariant under a ring
  automorphism.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring isomorphism induces a multiplicative isomorphism of the monoids of ideals. -/
def Ideal.mapMulEquiv (e : R ≃+* S) : Ideal R ≃* Ideal S where
  toFun I := I.map (e : R →+* S)
  invFun I := I.map (e.symm : S →+* R)
  left_inv _ := Ideal.map_of_equiv e
  right_inv I := by simpa using Ideal.map_of_equiv (I := I) e.symm
  map_mul' _ _ := Ideal.map_mul _ _ _

end

namespace Ideal

/-- `emultiplicity` of ideals is invariant under a ring automorphism. -/
theorem emultiplicity_map_ringEquiv {R : Type*} [CommRing R] (σ : R ≃+* R) (I J : Ideal R) :
    emultiplicity (Ideal.map σ I) (Ideal.map σ J) = emultiplicity I J := by
  exact emultiplicity_map_eq (Ideal.mapMulEquiv σ)

end Ideal

end
