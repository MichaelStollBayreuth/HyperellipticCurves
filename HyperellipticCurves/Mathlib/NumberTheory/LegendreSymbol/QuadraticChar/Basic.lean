/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Mathlib.Data.ZMod.IntUnitsPower
public import HyperellipticCurves.Mathlib.GroupTheory.QuotientGroup.UnitsModPow
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Square classes of a finite field

## Main statements

* `quadraticChar_toUnitHom_surjective`: for odd characteristic, the quadratic character maps the
  units onto `ℤˣ = {±1}`.
* `FiniteField.modPowTwoEquiv`: for odd characteristic, the quadratic character identifies
  `Fˣ/(Fˣ)²` with `ℤˣ = {±1}`.
* `FiniteField.modPowTwoEquivZModTwo`: for odd characteristic,
  `Fˣ/(Fˣ)² ≃* Multiplicative (ZMod 2)`, `0` for the squares and `1` for the nonsquares; its values
  are `FiniteField.modPowTwoEquivZModTwo_mk`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character of a finite field of odd characteristic maps the units onto
`ℤˣ = {±1}`: `-1` is a value (`quadraticChar_exists_neg_one`). -/
theorem quadraticChar_toUnitHom_surjective (hF : ringChar F ≠ 2) :
    Function.Surjective (quadraticChar F).toUnitHom := fun v ↦ by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  rcases Int.units_eq_one_or v with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨.mk0 a ha0, Units.ext (by simpa using ha)⟩

namespace FiniteField

/-- **Square classes of a finite field** `F` of odd characteristic: the quadratic character
identifies `Fˣ/(Fˣ)²` with `ℤˣ = {±1}`, its kernel being the squares
(`quadraticChar_one_iff_isSquare`), and it is onto (`quadraticChar_toUnitHom_surjective`). -/
noncomputable def modPowTwoEquiv (hF : ringChar F ≠ 2) : Units.ModPow F 2 ≃* ℤˣ :=
  QuotientGroup.liftEquiv _ (φ := (quadraticChar F).toUnitHom)
    (quadraticChar_toUnitHom_surjective F hF) <| by
    ext u
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff, Units.ModPow.mk_eq_one_iff_isSquare,
      ← quadraticChar_one_iff_isSquare u.ne_zero, Units.ext_iff, MulChar.coe_toUnitHom]
    rfl

variable {F}

@[simp]
theorem coe_modPowTwoEquiv_mk (hF : ringChar F ≠ 2) (u : Fˣ) :
    (modPowTwoEquiv F hF u : ℤ) = quadraticChar F u :=
  rfl

variable (F)

/-- **Square classes of a finite field** `F` of odd characteristic as `ℤ / 2`: `0` for the
squares, `1` for the nonsquares (`FiniteField.modPowTwoEquiv`, then
`Int.unitsMulEquivZModTwo`). -/
noncomputable def modPowTwoEquivZModTwo (hF : ringChar F ≠ 2) :
    Units.ModPow F 2 ≃* Multiplicative (ZMod 2) :=
  (modPowTwoEquiv F hF).trans Int.unitsMulEquivZModTwo

variable {F}

theorem modPowTwoEquivZModTwo_mk (hF : ringChar F ≠ 2) (u : Fˣ) :
    modPowTwoEquivZModTwo F hF u = .ofAdd (if IsSquare (u : F) then 0 else 1) := by
  have h := coe_modPowTwoEquiv_mk hF u
  rw [modPowTwoEquivZModTwo, MulEquiv.trans_apply]
  split_ifs with hu
  · rw [show modPowTwoEquiv F hF u = 1 from
      Units.ext (h.trans ((quadraticChar_one_iff_isSquare u.ne_zero).mpr hu))]
    rfl
  · rw [show modPowTwoEquiv F hF u = -1 from
      Units.ext (h.trans (quadraticChar_neg_one_iff_not_isSquare.mpr hu))]
    rfl

end FiniteField
