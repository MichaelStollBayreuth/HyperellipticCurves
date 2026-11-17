/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Elements of a fraction field as fractions

## Main statements

* `IsFractionRing.algebraMap_ne_zero`: a nonzero element of the ring stays nonzero in a fraction
  field.
* `IsFractionRing.exists_eq_div`: every element of a fraction field of a domain is a fraction of
  ring elements with nonzero denominator, in a form suited to `obtain ⟨p, q, hq, rfl⟩`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace IsFractionRing

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of a domain stays nonzero in a fraction field. -/
theorem algebraMap_ne_zero {c : R} (hc : c ≠ 0) : algebraMap R K c ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hc

variable [IsDomain R]

/-- Every element of a fraction field is a fraction of ring elements (with nonzero
denominator), in `∃`-form suitable for `obtain ⟨p, q, hq, rfl⟩` destructuring. -/
theorem exists_eq_div (x : K) :
    ∃ p q : R, q ≠ 0 ∧ x = algebraMap R K p / algebraMap R K q := by
  obtain ⟨p, q, hq, h⟩ := IsFractionRing.div_surjective (A := R) x
  exact ⟨p, q, nonZeroDivisors.ne_zero hq, h.symm⟩

end IsFractionRing

end
