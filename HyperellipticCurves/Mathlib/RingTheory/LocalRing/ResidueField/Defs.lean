/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Comparing elements of a local ring through their residues

## Main statements

* `IsLocalRing.ResidueField.invertibleTwo`: an `Invertible (2 : R)` descends to the residue
  field. The residue field is a `def`, not reducibly a quotient, so the instance for quotient
  rings does not apply to it.
* `IsLocalRing.residue_eq_of_sub_mem`: elements whose difference lies in the maximal ideal have
  the same residue.
* `IsLocalRing.isUnit_sub_of_residue_ne`: elements with distinct residues differ by a unit.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Invertibility of `2` descends to the residue field of a local ring. -/
noncomputable instance IsLocalRing.ResidueField.invertibleTwo {R : Type*} [CommRing R]
    [IsLocalRing R] [Invertible (2 : R)] : Invertible (2 : IsLocalRing.ResidueField R) :=
  (Invertible.map (IsLocalRing.residue R) 2).copy _ (map_ofNat _ 2).symm

namespace IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {p : ℕ}

/-- Elements whose difference lies in the maximal ideal have the same residue. -/
theorem residue_eq_of_sub_mem {a b : O} (h : a - b ∈ maximalIdeal O) :
    residue O a = residue O b := by
  rw [← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr h

/-- In a local ring, elements with distinct residues differ by a unit. -/
theorem isUnit_sub_of_residue_ne {a b : O} (h : residue O a ≠ residue O b) : IsUnit (a - b) :=
  notMem_maximalIdeal.mp fun hmem ↦ h (residue_eq_of_sub_mem hmem)

end IsLocalRing

end
