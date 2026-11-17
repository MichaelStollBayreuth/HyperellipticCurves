/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# Separability of fraction fields

## Main statements

* `FractionRing.isSeparable_of_isFractionRing`: separability of `F / K` passes to
  `FractionRing B / FractionRing R`, for fraction fields `K` of `R` and `F` of `B`.

Auxiliary material for `Ideal.relNorm_eq_pow_of_isMaximal` in the Selmer groups of the `x - T`
descent; upstreaming candidate for Mathlib.
-/

@[expose] public section

section FractionRing

attribute [local instance] FractionRing.liftAlgebra

variable (R K B F : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing B] [IsDomain B] [Algebra R B] [Module.IsTorsionFree R B] [Field F] [Algebra B F]
  [IsFractionRing B F] [Algebra K F] [Algebra R F] [IsScalarTower R K F] [IsScalarTower R B F]

/-- Separability of `F/K` passes to `FractionRing B / FractionRing R`, for fraction fields `K` of
`R` and `F` of `B`; the form in which `Ideal.relNorm_eq_pow_of_isMaximal` takes it. -/
theorem FractionRing.isSeparable_of_isFractionRing [Algebra.IsSeparable K F] :
    Algebra.IsSeparable (FractionRing R) (FractionRing B) :=
  .of_equiv_equiv (FractionRing.algEquiv R K).symm.toRingEquiv
    (FractionRing.algEquiv B F).symm.toRingEquiv
    (RingHom.ext (IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
      (FractionRing.algEquiv B F).symm))

end FractionRing
