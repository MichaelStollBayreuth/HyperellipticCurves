/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.RingTheory.PowerSeries.Inverse`: `IsAlgClosed`, for the statement
-- of `PowerSeries.instIsAlgClosedResidueField`.
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Division by series with unit constant coefficient, and the residue field of `k⟦X⟧`

The residue field of `k⟦X⟧` is `k` (`PowerSeries.residueFieldOfPowerSeries`); it inherits
algebraic closedness and `2 ≠ 0` from `k`.

## Main statements

* `PowerSeries.exists_mul_eq_of_constantCoeff_isUnit`: every power series is a multiple of a
  power series with unit constant coefficient.
* `PowerSeries.instIsAlgClosedResidueField`: the residue field of `k⟦X⟧` is algebraically closed
  when `k` is.
* `PowerSeries.instNeZeroTwoResidueField`: `2 ≠ 0` in the residue field of `k⟦X⟧` when `k` has
  characteristic zero.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace PowerSeries

section

variable {O : Type*} [CommRing O]

/-- Division in the power series ring by a series with unit constant coefficient. -/
theorem exists_mul_eq_of_constantCoeff_isUnit {O : Type*} [CommRing O] {D : PowerSeries O}
    (hD : IsUnit (PowerSeries.constantCoeff D)) (R : PowerSeries O) :
    ∃ m : PowerSeries O, m * D = R := by
  obtain ⟨v, hv⟩ := (PowerSeries.isUnit_iff_constantCoeff.mpr hD).exists_left_inv
  exact ⟨R * v, by rw [mul_assoc, hv, mul_one]⟩

end

open IsLocalRing

section

variable {k : Type*} [Field k]

/-- The residue field of `k⟦X⟧` is `k`, so it inherits algebraic closedness. -/
instance instIsAlgClosedResidueField [IsAlgClosed k] : IsAlgClosed (ResidueField k⟦X⟧) :=
  IsAlgClosed.of_ringEquiv k _ (residueFieldOfPowerSeries (k := k)).symm

/-- `2 ≠ 0` in the residue field of `k⟦X⟧`, which the hyperelliptic charts need. -/
instance instNeZeroTwoResidueField [CharZero k] : NeZero (2 : ResidueField k⟦X⟧) :=
  ⟨fun h ↦ two_ne_zero (α := k) <| by
    have := congrArg (residueFieldOfPowerSeries (k := k)) h
    rwa [map_ofNat, map_zero] at this⟩

end

end PowerSeries

end
