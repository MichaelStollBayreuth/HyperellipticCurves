/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The adic valuation of a unit

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_of_isUnit`: the `v`-adic valuation of a
  unit is `1`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R)

/-- The `v`-adic valuation of a unit is `1`. -/
theorem intValuation_eq_one_of_isUnit {a : R} (ha : IsUnit a) : v.intValuation a = 1 :=
  intValuation_eq_one_iff.mpr fun hmem ↦ v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ha)

end IsDedekindDomain.HeightOneSpectrum

end
