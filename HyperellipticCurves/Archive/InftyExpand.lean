/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.GlobalChart
public import HyperellipticCurves.Archive.Mathlib.Algebra.QuadraticAlgebra.Basic
public import HyperellipticCurves.Log.Charts.InfTransport

/-!
# The infinity-disk expansion homomorphism

The function-field counterpart of `HyperellipticCurves.Log.Charts.InfTransport`:
`ChabautyColeman.inftyExpand`, the ring homomorphism expanding a curve function on the
infinity disk (`x ↦ 1/u(z)`, `y ↦ 1/(u(z)^g·z)`), with its coordinate and base lemmas. The
main theorems do not depend on this file: the counting route identifies the expansions per
disk over `Frac(K⟦z⟧)`, without the function field.

Its ingredients are here as well: the evaluations `ChabautyColeman.invAevalFracHom` on
`K[X]` and `ChabautyColeman.invAevalRatFuncHom` on `K(x)` at the pole coordinate `1/u(z)`,
and the square certificate `ChabautyColeman.sq_inv_pow_mul_X` — that `1/(u(z)^g·z)` squares
to the image of `fK`, the reflected on-curve identity, from the defining equation of `u`
alone. The reflection/pole-order half (`ChabautyColeman.aeval_inv_eq_zero_iff` and friends)
lives in `HyperellipticCurves.Log.Charts.InfTransport`, consumed by
`HyperellipticCurves.Log.Trace.TraceKzInf`.
-/

@[expose] public section

open Polynomial PowerSeries
open scoped PowerSeries

namespace ChabautyColeman

section InftyExpandHom

open HypField

variable {K : Type*} [Field K] {fK : K[X]} {u : K⟦X⟧} {g : ℕ}

/-- The evaluation `K[X] → Frac(K⟦z⟧)` at the pole coordinate `1/u(z)`. -/
noncomputable def invAevalFracHom (u : K⟦X⟧) : K[X] →+* FractionRing (PowerSeries K) :=
  (aeval ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u)⁻¹)).toRingHom

theorem invAevalFracHom_apply (u : K⟦X⟧) (p : K[X]) :
    invAevalFracHom u p
      = aeval ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u)⁻¹) p := rfl

theorem invAevalFracHom_injective (hfKm : fK.Monic)
    (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse) :
    Function.Injective (invAevalFracHom u) := fun p q h ↦
  sub_eq_zero.mp ((aeval_inv_eq_zero_iff hfKm hueq).mp
    (by rw [map_sub, sub_eq_zero]; exact h))

/-- The evaluation of a rational function at the pole coordinate `1/u(z)`: the extension of
`ChabautyColeman.invAevalFracHom` to the field of rational functions. -/
noncomputable def invAevalRatFuncHom (hfKm : fK.Monic)
    (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse) :
    RatFunc K →+* FractionRing (PowerSeries K) :=
  IsFractionRing.lift (invAevalFracHom_injective hfKm hueq)

@[simp]
theorem invAevalRatFuncHom_algebraMap (hfKm : fK.Monic)
    (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse) (p : K[X]) :
    invAevalRatFuncHom hfKm hueq (algebraMap K[X] (RatFunc K) p) = invAevalFracHom u p :=
  IsFractionRing.lift_algebraMap _ p

/-- The square certificate for the infinity-disk expansion: the value
`1/(u(z)^g·z)` of the coordinate `y` squares to the image of `fK`. -/
theorem sq_inv_pow_mul_X (hfKm : fK.Monic) (hdeg : fK.natDegree = 2 * g + 1)
    (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse) :
    ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u ^ g
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X)⁻¹) ^ 2
      = invAevalRatFuncHom hfKm hueq (algebraMap K[X] (RatFunc K) fK)
        + invAevalRatFuncHom hfKm hueq (0 : RatFunc K)
          * (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u ^ g
            * algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X)⁻¹ := by
  obtain ⟨hu0, hune⟩ := ne_zero_of_eq_X_sq_mul hfKm hueq
  set Kz := FractionRing (PowerSeries K)
  have hKinj : Function.Injective (algebraMap (PowerSeries K) Kz) :=
    IsFractionRing.injective (PowerSeries K) Kz
  have hxne : algebraMap (PowerSeries K) Kz u ≠ 0 := fun h ↦
    hune (hKinj (by rw [h, map_zero]))
  have hXne : algebraMap (PowerSeries K) Kz PowerSeries.X ≠ 0 := fun h ↦
    PowerSeries.X_ne_zero (hKinj (by rw [h, map_zero]))
  rw [map_zero, zero_mul, add_zero, invAevalRatFuncHom_algebraMap]
  -- the reflected evaluation identity, with `reflect (natDegree fK) fK = fK.reverse`
  let : Invertible (algebraMap (PowerSeries K) Kz u) := invertibleOfNonzero hxne
  have hrefl := eval₂_reflect_mul_pow (algebraMap K Kz)
    (algebraMap (PowerSeries K) Kz u) fK.natDegree fK.reverse
    (natDegree_reflect_le.trans (by simp))
  rw [show fK.reverse.reflect fK.natDegree = fK by rw [Polynomial.reverse, reflect_reflect],
    invOf_eq_inv] at hrefl
  have heval : Polynomial.eval₂ (algebraMap K Kz)
      (algebraMap (PowerSeries K) Kz u) fK.reverse
      = algebraMap (PowerSeries K) Kz (aeval u fK.reverse) :=
    (aeval_def _ _).symm.trans (aeval_algebraMap_apply _ u fK.reverse)
  rw [heval] at hrefl
  -- the defining equation of `u`, mapped into the fraction field
  have hueqKz : algebraMap (PowerSeries K) Kz u
      = algebraMap (PowerSeries K) Kz PowerSeries.X ^ 2
        * algebraMap (PowerSeries K) Kz (aeval u fK.reverse) := by
    rw [← map_pow, ← map_mul, ← hueq]
  -- assemble in the field
  have hval : invAevalFracHom u fK
      = Polynomial.eval₂ (algebraMap K Kz)
        ((algebraMap (PowerSeries K) Kz u)⁻¹) fK := by
    rw [invAevalFracHom_apply, aeval_def]
  rw [hval]
  rw [hdeg] at hrefl
  rw [inv_pow]
  refine inv_eq_of_mul_eq_one_right ?_
  refine mul_left_cancel₀ hxne ?_
  rw [mul_one]
  calc algebraMap (PowerSeries K) Kz u
      * ((algebraMap (PowerSeries K) Kz u ^ g
          * algebraMap (PowerSeries K) Kz PowerSeries.X) ^ 2
        * Polynomial.eval₂ (algebraMap K Kz) ((algebraMap (PowerSeries K) Kz u)⁻¹) fK)
      = algebraMap (PowerSeries K) Kz PowerSeries.X ^ 2
        * (Polynomial.eval₂ (algebraMap K Kz) ((algebraMap (PowerSeries K) Kz u)⁻¹) fK
          * algebraMap (PowerSeries K) Kz u ^ (2 * g + 1)) := by ring
    _ = algebraMap (PowerSeries K) Kz PowerSeries.X ^ 2
        * algebraMap (PowerSeries K) Kz (aeval u fK.reverse) := by rw [hrefl]
    _ = algebraMap (PowerSeries K) Kz u := hueqKz.symm

variable (hfKm : fK.Monic) (hdeg : fK.natDegree = 2 * g + 1)

variable (fK u g) in
/-- **The infinity-disk expansion homomorphism on the function field**: the ring
homomorphism `F_K →+* Frac(K⟦z⟧)` expanding a curve function on the residue disk around
infinity: `x ↦ 1/u(z)` and `y ↦ 1/(u(z)^g·z)`, for the pole coordinate `u` solving
`u = z²·F(u)`, `F = reverse fK`. The analogue at the infinity centre of
`ChabautyColeman.globExpand` and `ChabautyColeman.weierstrassExpand`. -/
noncomputable def inftyExpand (hfKm : fK.Monic) (hdeg : fK.natDegree = 2 * g + 1)
    (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse) :
    HypField K fK →+* FractionRing (PowerSeries K) :=
  QuadraticAlgebra.liftRingHom (invAevalRatFuncHom hfKm hueq)
    ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u ^ g
      * algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X)⁻¹)
    (sq_inv_pow_mul_X hfKm hdeg hueq)

variable (hfKm : fK.Monic) (hdeg : fK.natDegree = 2 * g + 1)
  (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse)

theorem inftyExpand_algebraMap (r : RatFunc K) :
    inftyExpand fK u g hfKm hdeg hueq (algebraMap (RatFunc K) (HypField K fK) r)
      = invAevalRatFuncHom hfKm hueq r :=
  RingHom.congr_fun (QuadraticAlgebra.liftRingHom_comp_algebraMap _ _
    (sq_inv_pow_mul_X hfKm hdeg hueq)) r

theorem inftyExpand_algebraMap_polynomial (p : K[X]) :
    inftyExpand fK u g hfKm hdeg hueq (algebraMap K[X] (HypField K fK) p)
      = aeval ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u)⁻¹) p := by
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K fK), inftyExpand_algebraMap,
    invAevalRatFuncHom_algebraMap]
  rfl

theorem inftyExpand_algebraMap_base (c : K) :
    inftyExpand fK u g hfKm hdeg hueq (algebraMap K (HypField K fK) c)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.C c) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (HypField K fK), inftyExpand_algebraMap_polynomial,
    Polynomial.algebraMap_eq, aeval_C]
  rw [show algebraMap K (FractionRing (PowerSeries K)) c
    = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (algebraMap K (PowerSeries K) c)
    from (IsScalarTower.algebraMap_apply K (PowerSeries K) _ c)]
  rfl

theorem inftyExpand_x :
    inftyExpand fK u g hfKm hdeg hueq (HypField.x fK)
      = (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u)⁻¹ := by
  rw [HypField.x, inftyExpand_algebraMap_polynomial, aeval_X]

theorem inftyExpand_y :
    inftyExpand fK u g hfKm hdeg hueq (HypField.y fK)
      = (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u ^ g
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X)⁻¹ :=
  QuadraticAlgebra.liftRingHom_omega _ _ (sq_inv_pow_mul_X hfKm hdeg hueq)

end InftyExpandHom

end ChabautyColeman

end
