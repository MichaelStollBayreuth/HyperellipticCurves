/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Squarefreeness ascends to the fraction field

## Main statements

* `Polynomial.Monic.squarefree_map_fraction_map`: a monic squarefree polynomial over an
  integrally closed domain stays squarefree over the fraction field (Gauss's lemma).

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

open Polynomial

namespace Polynomial

/-- **Squarefreeness ascends to the fraction field** for a monic polynomial over an
integrally closed domain: a repeated monic factor over the fraction field lifts to a
repeated factor by Gauss's lemma. -/
theorem Monic.squarefree_map_fraction_map {R K : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {g : R[X]}
    (hg : g.Monic) (hsq : Squarefree g) : Squarefree (g.map (algebraMap R K)) := fun q hq ↦ by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact (hg.map (algebraMap R K)).ne_zero (zero_dvd_iff.mp (by simpa using hq))
  have hqm := monic_mul_leadingCoeff_inv hq0
  have hassoc : Associated q (q * C q.leadingCoeff⁻¹) :=
    ⟨(isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0)).isUnit).unit, rfl⟩
  have hdvd := (hassoc.mul_mul hassoc).symm.dvd.trans hq
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hg ((dvd_mul_right _ _).trans hdvd)
  rw [hqm.leadingCoeff, map_one, mul_one] at hQ
  have hQm : Q.Monic := monic_of_injective (IsFractionRing.injective R K) (hQ ▸ hqm)
  refine hassoc.symm.isUnit (hQ ▸ ((hsq Q ?_).map (mapRingHom (algebraMap R K))))
  exact hg.dvd_of_fraction_map_dvd_fraction_map (K := K) (hQm.mul hQm)
    (by rwa [Polynomial.map_mul, hQ])

end Polynomial

end
