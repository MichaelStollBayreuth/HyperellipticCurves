/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Complete local rings are Henselian; squares in Henselian local rings

## Main statements

* `IsAdicComplete.henselianLocalRing`: a local ring complete at its maximal ideal is Henselian.
* `HenselianLocalRing.isSquare_iff_isSquare_residue`: if `2` is a unit, a unit is a square iff its
  residue is.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

open IsLocalRing Polynomial

/-- A local ring that is adically complete at its maximal ideal is Henselian, by
`IsAdicComplete.henselianRing`. -/
instance (priority := 100) IsAdicComplete.henselianLocalRing (R : Type*) [CommRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _))

/-- **Squares in a Henselian local ring**: if `2` is a unit, a unit is a square exactly when its
residue is, by Hensel's lemma for `X ^ 2 - u`, whose derivative `2 X` is a unit at a lift of the
square root. -/
theorem HenselianLocalRing.isSquare_iff_isSquare_residue {R : Type*} [CommRing R]
    [HenselianLocalRing R] (h2 : IsUnit (2 : R)) {u : R} (hu : IsUnit u) :
    IsSquare u ↔ IsSquare (residue R u) := by
  refine ⟨fun h ↦ h.map (residue R), fun ⟨r, hr⟩ ↦ ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective r
  have hb : IsUnit b := isUnit_of_map_unit (residue R) b (isUnit_of_mul_isUnit_left (hr ▸ hu.map _))
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u)
    (monic_X_pow_sub_C u two_ne_zero) b ((residue_eq_zero_iff _).mp (by simp [hr, sq]))
    (by simpa [one_add_one_eq_two] using h2.mul hb)
  exact ⟨a, by simpa [sub_eq_zero, sq, eq_comm] using ha⟩

end
