/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Squares in an integrally closed domain

## Main statements

* `IsIntegrallyClosed.isSquare_algebraMap_iff`: an element of an integrally closed domain is a
  square if and only if it is a square in the fraction field.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace IsIntegrallyClosed

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
  [IsIntegrallyClosed R]

/-- A square root in the fraction field of an element of an integrally closed domain is
integral, so it lies in the domain. -/
theorem isSquare_algebraMap_iff {r : R} : IsSquare (algebraMap R K r) ↔ IsSquare r := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, (·.map _)⟩
  obtain ⟨y, rfl⟩ := exists_algebraMap_eq_of_isIntegral_pow two_pos
    (sq x ▸ hx ▸ isIntegral_algebraMap (R := R) (x := r))
  exact ⟨y, IsFractionRing.injective R K (by rw [hx, map_mul])⟩

end IsIntegrallyClosed

end
