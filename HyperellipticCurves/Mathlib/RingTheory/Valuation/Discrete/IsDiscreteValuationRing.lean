/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The height one prime of a discrete valuation ring

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal`: the maximal ideal is the only height one
  prime of a discrete valuation ring.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`); upstreaming candidate for
Mathlib.
-/

@[expose] public section

/-- The maximal ideal is the only height one prime of a discrete valuation ring. -/
theorem IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (P : HeightOneSpectrum A) :
    P = IsDiscreteValuationRing.maximalIdeal A :=
  HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal P.isMaximal)
