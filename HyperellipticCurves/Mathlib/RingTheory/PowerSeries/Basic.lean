/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Constant coefficients, reduction, and the characteristic of power series

## Main statements

* `PowerSeries.constantCoeff_map`: the univariate counterpart of
  `MvPowerSeries.constantCoeff_map`.
* `PowerSeries.constantCoeff_aeval`: the constant coefficient of a polynomial evaluated at a
  power series is the polynomial evaluated at the constant coefficient.
* `PowerSeries.map_aeval`: reduction of the coefficients commutes with evaluating a polynomial at
  a power series.
* `PowerSeries.instCharZero`: `k⟦X⟧` has characteristic zero when `k` has (its fraction field
  then has it by Mathlib's `IsFractionRing.charZero`).

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial

namespace PowerSeries

/-- The univariate counterpart of `MvPowerSeries.constantCoeff_map`. -/
@[simp]
theorem constantCoeff_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (φ : R⟦X⟧) :
    constantCoeff (map f φ) = f (constantCoeff φ) :=
  rfl

section

variable {O : Type*} [CommRing O]

/-- The constant coefficient of `aeval x p` (a polynomial evaluated at a power series) is the
value of `p` at the constant coefficient of `x`. -/
theorem constantCoeff_aeval (p : O[X]) (x : O⟦X⟧) :
    constantCoeff (Polynomial.aeval x p) = p.eval (constantCoeff x) := by
  have h1 : (constantCoeff : O⟦X⟧ →+* O).comp (algebraMap O (O⟦X⟧)) = RingHom.id O :=
    RingHom.ext fun r ↦ constantCoeff_C r
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, Polynomial.eval₂_id]

/-- Reduction commutes with evaluation of a polynomial at a power series. -/
theorem map_aeval {O κ' : Type*} [CommRing O] [CommRing κ'] (ρ : O →+* κ') (s : O⟦X⟧) (p : O[X]) :
    (PowerSeries.map ρ) (Polynomial.aeval s p)
      = Polynomial.aeval ((PowerSeries.map ρ) s) (p.map ρ) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def, eval₂_map]
  congr 1
  ext a
  simp [PowerSeries.algebraMap_eq, PowerSeries.map_C]

end

section

variable {k : Type*} [Field k]

/-- Characteristic zero passes to `k⟦X⟧` along the constant coefficient. -/
instance instCharZero [CharZero k] : CharZero k⟦X⟧ :=
  (constantCoeff : k⟦X⟧ →+* k).charZero

end

end PowerSeries

end
