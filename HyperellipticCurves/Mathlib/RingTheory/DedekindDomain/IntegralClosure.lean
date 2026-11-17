/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The integral closure of a Dedekind domain in `K[X] ⧸ (g)`

Let `R` be a domain with fraction field `K` and `g : K[X]` irreducible. Mathlib's
`integralClosure.isDedekindDomain` and `integralClosure.isFractionRing_of_finite_extension`
cannot be instances, since `K` cannot be inferred from `integralClosure R L`. For
`L = AdjoinRoot g` it can, and this file provides the instances.

## Main statements

* `AdjoinRoot.isFractionRing_integralClosure`: `K[X] ⧸ (g)` is the fraction field of the integral
  closure of `R` in it.
* `AdjoinRoot.isDedekindDomain_integralClosure`: for `R` Dedekind and `K[X] ⧸ (g)` separable over
  `K` (automatic for a perfect field `K`, by `Algebra.IsAlgebraic.isSeparable_of_perfectField`),
  the integral closure is a Dedekind domain.
* `AdjoinRoot.isTorsionFree`: `K[X] ⧸ (g)`, and hence the integral closure, is torsion-free
  over `R`.

Generalized from EllipticCurves (`EllipticCurves/WeakMordellWeil.lean`, the instances on
`ringOfIntegersFactor`), for the Selmer groups of the field factors of `K[X] ⧸ (f)`; upstreaming
candidates for Mathlib.
-/

@[expose] public section

open Polynomial

namespace AdjoinRoot

instance isFractionRing_integralClosure (R : Type*) [CommRing R] [IsDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K] (g : K[X]) [Fact (Irreducible g)] :
    IsFractionRing (integralClosure R (AdjoinRoot g)) (AdjoinRoot g) :=
  have := (powerBasis (Fact.out : Irreducible g).ne_zero).finite
  integralClosure.isFractionRing_of_finite_extension K (AdjoinRoot g)

instance isDedekindDomain_integralClosure (R : Type*) [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (g : K[X]) [Fact (Irreducible g)]
    [Algebra.IsSeparable K (AdjoinRoot g)] :
    IsDedekindDomain (integralClosure R (AdjoinRoot g)) :=
  have := (powerBasis (Fact.out : Irreducible g).ne_zero).finite
  integralClosure.isDedekindDomain R K (AdjoinRoot g)

/-- `K[X] ⧸ (g)` is torsion-free over `R`; with Mathlib's `Subalgebra.instIsTorsionFree`, so is the
integral closure of `R` in it. -/
instance isTorsionFree (R : Type*) [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (g : K[X]) [Fact (Irreducible g)] :
    Module.IsTorsionFree R (AdjoinRoot g) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R K]
  exact (algebraMap K (AdjoinRoot g)).injective.comp (IsFractionRing.injective R K)

end AdjoinRoot
