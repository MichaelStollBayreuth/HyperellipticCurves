/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.GlobalChart
public import HyperellipticCurves.Archive.Mathlib.Algebra.QuadraticAlgebra.Basic
public import HyperellipticCurves.Log.Analytic.OmegaPrime
public import HyperellipticCurves.Log.Charts.DiskTransport
public import HyperellipticCurves.Log.Charts.PhiChart

import Mathlib.Tactic.FieldSimp

/-!
# The generic disk expansion of the function field

The function-field counterpart of `HyperellipticCurves.Log.Charts.DiskTransport`: the
disk-expansion homomorphism `ChabautyColeman.globExpand` at a generic centre, the block and
pipeline transports along it, the chain rule, and the taylor-form endpoint
`ChabautyColeman.omegaPrime_taylor`. The main theorems do not depend on this file: the counting
route identifies the expansions per disk over `Frac(K⟦z⟧)`
(`HyperellipticCurves.Log.Trace.TraceKz`), without the function field.
-/

@[expose] public section

open Polynomial
open scoped PowerSeries

namespace ChabautyColeman

section ExpandHom

variable {K : Type*} [Field K]

open HypField

/-- The composite `K[X] → K⟦X⟧ → Frac(K⟦X⟧)`, Taylor expansion at `a` followed by the
inclusion into the fraction field. -/
noncomputable def taylorFracHom (a : K) : K[X] →+* FractionRing (PowerSeries K) :=
  (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (taylorSeriesHom a)

theorem taylorFracHom_injective (a : K) : Function.Injective (taylorFracHom a) :=
  (IsFractionRing.injective (PowerSeries K) _).comp (taylorSeriesHom_injective a)

variable [NeZero (2 : K)]

/-- The square-root certificate for the disk-expansion homomorphism: `(b·η)²` is the image
of the defining coefficient `f` of the function field. -/
theorem sq_algebraMap_C_mul_diskSeriesGeneric {f : K[X]} {a b : K}
    (hb : b ^ 2 = f.eval a) (hfa : f.eval a ≠ 0) :
    algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
        (PowerSeries.C b * diskSeriesGeneric f a) ^ 2
      = IsFractionRing.lift (taylorFracHom_injective (K := K) a)
          (algebraMap K[X] (RatFunc K) f)
        + IsFractionRing.lift (taylorFracHom_injective (K := K) a) (0 : RatFunc K)
          * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (PowerSeries.C b * diskSeriesGeneric f a) := by
  have hfa' : IsUnit (f.eval a) := isUnit_iff_ne_zero.mpr hfa
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
  rw [map_zero, zero_mul, add_zero, IsFractionRing.lift_algebraMap]
  rw [taylorFracHom, RingHom.comp_apply, taylorSeriesHom_apply, ← map_pow]
  congr 1
  rw [mul_pow, diskSeriesGeneric_sq hfa' h2, ← map_pow, hb]
  have hinv : (PowerSeries.C (f.eval a) : PowerSeries K)
      * PowerSeries.C (Ring.inverse (f.eval a)) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hfa', map_one]
  linear_combination ((taylor a f : PowerSeries K)) * hinv

/-- **The disk-expansion homomorphism on the function field**: the ring homomorphism
`F_K →+* Frac(K⟦z⟧)` expanding a curve function on the residue disk around the point
`(a, b)`: on `K(x)` it is Taylor expansion at `a` (i.e. `x ↦ a + z`), and
`y ↦ b·η` with `η` the normalized square-root series of `f` at `a`
(`ChabautyColeman.diskSeriesGeneric`). -/
noncomputable def globExpand (f : K[X]) (a b : K) (hb : b ^ 2 = f.eval a)
    (hfa : f.eval a ≠ 0) :
    HypField K f →+* FractionRing (PowerSeries K) :=
  QuadraticAlgebra.liftRingHom (IsFractionRing.lift (taylorFracHom_injective (K := K) a))
    (algebraMap (PowerSeries K) _ (PowerSeries.C b * diskSeriesGeneric f a))
    (sq_algebraMap_C_mul_diskSeriesGeneric hb hfa)

variable {f : K[X]} {a b : K} (hb : b ^ 2 = f.eval a) (hfa : f.eval a ≠ 0)

theorem globExpand_algebraMap (r : RatFunc K) :
    globExpand f a b hb hfa (algebraMap (RatFunc K) (HypField K f) r)
      = IsFractionRing.lift (taylorFracHom_injective (K := K) a) r := by
  exact RingHom.congr_fun (QuadraticAlgebra.liftRingHom_comp_algebraMap _ _
    (sq_algebraMap_C_mul_diskSeriesGeneric hb hfa)) r

theorem globExpand_algebraMap_polynomial (p : K[X]) :
    globExpand f a b hb hfa (algebraMap K[X] (HypField K f) p)
      = algebraMap (PowerSeries K) _ (taylor a p : PowerSeries K) := by
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f), globExpand_algebraMap,
    IsFractionRing.lift_algebraMap]
  rfl

theorem globExpand_algebraMap_base (c : K) :
    globExpand f a b hb hfa (algebraMap K (HypField K f) c)
      = algebraMap (PowerSeries K) _ (PowerSeries.C c) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (HypField K f), globExpand_algebraMap_polynomial,
    Polynomial.algebraMap_eq, taylor_C, Polynomial.coe_C]

theorem globExpand_x :
    globExpand f a b hb hfa (x f)
      = algebraMap (PowerSeries K) _ (PowerSeries.C a + PowerSeries.X) := by
  rw [x, globExpand_algebraMap_polynomial, taylor_X, Polynomial.coe_add, Polynomial.coe_X,
    Polynomial.coe_C, add_comm]

theorem globExpand_y :
    globExpand f a b hb hfa (y f)
      = algebraMap (PowerSeries K) _ (PowerSeries.C b * diskSeriesGeneric f a) :=
  QuadraticAlgebra.liftRingHom_omega _ _ (sq_algebraMap_C_mul_diskSeriesGeneric hb hfa)

/-- On the coordinate ring, the disk-expansion homomorphism is the componentwise expansion
`ChabautyColeman.funcExpansionGeneric`. -/
theorem globExpand_toHypField (w : HypRing K f) :
    globExpand f a b hb hfa (HypRing.toHypField f w)
      = algebraMap (PowerSeries K) _ (funcExpansionGeneric f w.re w.im a b) := by
  rw [HypRing.toHypField_apply, map_add, map_mul, globExpand_algebraMap_polynomial,
    globExpand_algebraMap_polynomial, globExpand_y, funcExpansionGeneric, map_add]
  simp only [map_mul]
  ring

end ExpandHom

section BlockTransport

open HypField

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {a b xQ yQ m₀ : O} {m : O⟦X⟧}
  (hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)) (hfaK : (f.map ψ).eval (ψ a) ≠ 0)

/-- The two transports agree on the base ring: expanding a global constant gives the
constant series. -/
theorem globExpand_algebraMap_base_comp (c : O) :
    globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (algebraMap K (HypField K (f.map ψ)) (ψ c))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) (PowerSeries.C c) := by
  rw [globExpand_algebraMap_base, RingHom.comp_apply, PowerSeries.map_C]

/-- **Transport of a constant block**: a global datum with coefficients in the base expands
to the constant-series datum. -/
theorem map_globExpand_map_algebraMap (p : O[X]) :
    ((p.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map
        (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = (p.map (PowerSeries.C : O →+* O⟦X⟧)).map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
            (PowerSeries.map ψ)) := by
  simp only [Polynomial.map_map]
  exact congrArg (Polynomial.map · p)
    (RingHom.ext (globExpand_algebraMap_base_comp hbK hfaK))

/-- The coordinate `x` expands to the disk parameter around the centre. -/
theorem globExpand_x_eq_diskX :
    globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (HypField.x (f.map ψ))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) (PowerSeries.C a + PowerSeries.X) := by
  rw [globExpand_x, RingHom.comp_apply]
  simp only [map_add, PowerSeries.map_C, PowerSeries.map_X]

/-- The coordinate `y` expands to `b·η(z)`. -/
theorem globExpand_y_eq_diskY (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (HypField.y (f.map ψ))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) (PowerSeries.C b * diskSeriesGeneric f a) := by
  rw [globExpand_y, RingHom.comp_apply]
  simp only [map_mul, PowerSeries.map_C, map_diskSeriesGeneric ψ f a hfa h2]

/-- **Transport of the constant pair block**, `u`-part. -/
theorem map_globExpand_globU₃ :
    (globU₃ (f.map ψ) (ψ a) (ψ xQ)).map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = (phiU₃ a xQ).map ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) := by
  rw [globU₃, phiU₃,
    show ((X - C (ψ xQ)) * (X - C (ψ a)) : K[X]) = ((X - C xQ) * (X - C a)).map ψ by simp,
    ← map_globExpand_map_algebraMap hbK hfaK ((X - C xQ) * (X - C a))]

/-- **Transport of the constant pair block**, `v`-part. -/
theorem map_globExpand_globV₃ :
    (globV₃ (f.map ψ) (ψ xQ) (ψ yQ) (ψ m₀)).map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = (phiV₃ xQ yQ m₀).map ((algebraMap (PowerSeries K)
          (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)) := by
  rw [globV₃, phiV₃, ← pairV_map, ← map_globExpand_map_algebraMap hbK hfaK (pairV xQ yQ m₀)]

variable [Fact (Odd (f.map ψ).natDegree)]

/-- The global slope of the moving pair expands to the disk slope certificate `m`. -/
theorem globExpand_globSlope_eq
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (globSlope (f.map ψ) (ψ xQ) (ψ yQ))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) m := by
  set ρ' : O⟦X⟧ →+* FractionRing (PowerSeries K)
    := (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
      (PowerSeries.map ψ) with hρdef
  have hDne : ρ' (PowerSeries.C xQ) - ρ' (PowerSeries.C a + PowerSeries.X) ≠ 0 := by
    rw [← map_sub, hρdef, RingHom.comp_apply]
    refine (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr fun h0 ↦ ?_
    have h1 := congrArg (PowerSeries.coeff 1) h0
    simp at h1
  have h1 := congrArg (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
    (globSlope_spec (f.map ψ) (ψ xQ) (ψ yQ))
  rw [map_mul, map_sub, map_sub, globExpand_algebraMap_base_comp hbK hfaK xQ,
    globExpand_x_eq_diskX hbK hfaK, ← map_neg ψ yQ,
    globExpand_algebraMap_base_comp hbK hfaK (-yQ),
    globExpand_y_eq_diskY hbK hfaK hfa h2] at h1
  have h2' := congrArg ρ' hm
  rw [map_mul, map_sub, map_sub] at h2'
  exact mul_right_cancel₀ hDne (h1.trans h2'.symm)

/-- **Transport of the moving pair block**, `u`-part. -/
theorem map_globExpand_globU₁ :
    (globU₁ (f.map ψ) (ψ xQ)).map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = (phiU₁ a xQ).map ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) := by
  simp only [globU₁, phiU₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, globExpand_x_eq_diskX hbK hfaK,
    globExpand_algebraMap_base_comp hbK hfaK xQ]

/-- **Transport of the moving pair block**, `v`-part. -/
theorem map_globExpand_globV₁
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    (globV₁ (f.map ψ) (ψ xQ) (ψ yQ)).map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = (phiV₁ f a b m).map ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) := by
  rw [globV₁, phiV₁, pairV_map, pairV_map, globExpand_x_eq_diskX hbK hfaK,
    globExpand_y_eq_diskY hbK hfaK hfa h2, globExpand_globSlope_eq hbK hfaK hm hfa h2]

/-- **The global three-block configuration expands to the per-disk one**: the six blockwise
identifications above, as one equation between configurations. This is the form the
certificate descents consume (`ChabautyColeman.PipelineData.blocks_of_map_eq` recovers the
individual blocks). -/
theorem map_globExpand_globConfig {uτ vτ : O[X]}
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)).map
        (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = (phiConfig f a b xQ yQ m m₀ uτ vτ).map
        ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)) :=
  PipelineData.map_eq_of_blocks (map_globExpand_globU₁ hbK hfaK)
    (map_globExpand_globV₁ hbK hfaK hm hfa h2) (map_globExpand_map_algebraMap hbK hfaK uτ)
    (map_globExpand_map_algebraMap hbK hfaK vτ) (map_globExpand_globU₃ hbK hfaK)
    (map_globExpand_globV₃ hbK hfaK)

end BlockTransport

section Transport

open HypField

variable {O : Type*} [CommRing O] [Nontrivial O] {K : Type*} [Field K] [CharZero K]
  [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

/-- **Disk-expansion transport for the chart pipeline**: expanding the global pipeline (run
at the generic point of the curve over `K`) on the residue disk around `(a, b)` yields
exactly the per-disk `φ`-pipeline. Both sides are compared inside `Frac(K⟦z⟧)`; the
certificates are transported separately on each side, and the outputs agree by uniqueness of
reduced representatives (certificate-independence). -/
theorem map_globExpand_globPipeline
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)) (hfaK : (f.map ψ).eval (ψ a) ≠ 0)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree) :
    ((globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg).1.map
        (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK),
      (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg).2.map
        (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK))
      = ((phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)),
        (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2.map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
            (PowerSeries.map ψ))) := by
  classical
  -- the seven input identifications: `E` on the global data is `ρ'` on the disk data
  have hFeq := map_globExpand_map_algebraMap hbK hfaK f
  have hU₁ := map_globExpand_globU₁ (xQ := xQ) hbK hfaK
  have hV₁ := map_globExpand_globV₁ hbK hfaK hm hfa h2
  have hU₂ := map_globExpand_map_algebraMap hbK hfaK uτ
  have hV₂ := map_globExpand_map_algebraMap hbK hfaK vτ
  have hU₃ := map_globExpand_globU₃ (xQ := xQ) hbK hfaK
  have hV₃ := map_globExpand_globV₃ (xQ := xQ) (yQ := yQ) (m₀ := m₀) hbK hfaK
  set Kz := FractionRing (PowerSeries K) with hKzdef
  set E := globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK with hEdef
  set ρ' : O⟦X⟧ →+* Kz
    := (algebraMap (PowerSeries K) Kz).comp (PowerSeries.map ψ) with hρdef
  -- the common coefficient map `O →+* Kz`
  set χ : O →+* Kz := ρ'.comp (PowerSeries.C : O →+* O⟦X⟧) with hχdef
  -- ambient facts over `Kz`
  have hinj : Function.Injective (algebraMap (PowerSeries K) Kz) :=
    IsFractionRing.injective (PowerSeries K) Kz
  have hchPS : CharZero (PowerSeries K) := (PowerSeries.constantCoeff : K⟦X⟧ →+* K).charZero
  have hchKz : CharZero Kz := charZero_of_injective_algebraMap hinj
  have h2Kz : NeZero (2 : Kz) := ⟨by norm_num⟩
  -- the phi-side input facts over `O⟦X⟧`
  set F : (O⟦X⟧)[X] := f.map PowerSeries.C with hFdef
  have hu₁ : (phiU₁ a xQ (O := O)).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hu₃ : (phiU₃ a xQ (O := O)).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₁ : phiU₁ a xQ ∣ phiV₁ f a b m ^ 2 - F := movingPair_dvd hsep hm hb hfa h2 hyQ
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧) ∣ (vτ.map PowerSeries.C) ^ 2 - F :=
    map_dvd_sq_sub _ hdvdτ
  have hsepn : IsUnit (a - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hd₃ : phiU₃ a xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - F :=
    map_dvd_sq_sub _ (pair_dvd hsepn hm₀ hyQ (by rwa [neg_pow_two]))
  -- the glob-side input facts over the function field
  have hyQK : (ψ yQ) ^ 2 = (f.map ψ).eval (ψ xQ) := map_sq_eq_eval_map ψ hyQ
  have hsepK : ψ a ≠ ψ xQ := map_ne_of_isUnit_sub ψ hsep
  have hm₀K : (ψ m₀) * (ψ a - ψ xQ) = -(ψ b) - ψ yQ := map_slope ψ hm₀
  have hu₁g : (globU₁ (f.map ψ) (ψ xQ)).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂g : ((uτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))).Monic :=
    (huτ.map ψ).map _
  have hu₃g : (globU₃ (f.map ψ) (ψ a) (ψ xQ)).Monic :=
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hdvdτK : uτ.map ψ ∣ (vτ.map ψ) ^ 2 - f.map ψ :=
    map_dvd_sq_sub ψ hdvdτ
  have hd₁g := globPair_dvd (f.map ψ) hyQK
  have hd₂g : (uτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))
      ∣ ((vτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))) ^ 2
        - (f.map ψ).map (algebraMap K (HypField K (f.map ψ))) :=
    map_dvd_sq_sub _ hdvdτK
  have hd₃g := globPair₃_dvd (f.map ψ) hsepK hm₀K hbK hyQK
  -- pipelines mapped into `Kz`
  have hmapE := map_cantorPipeline_generic E hu₁g hu₂g hu₃g hcertsg
  have hmapP := map_cantorPipeline_generic ρ' hu₁ hu₂ hu₃ hcerts
  -- monic/dvd facts for the common inputs over `Kz`, phi-side spelling
  have hu₁z : ((phiU₁ a xQ).map ρ').Monic := hu₁.map ρ'
  have hu₂z : ((uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ').Monic := hu₂.map ρ'
  have hu₃z : ((phiU₃ a xQ).map ρ').Monic := hu₃.map ρ'
  have hd₁z : (phiU₁ a xQ).map ρ' ∣ ((phiV₁ f a b m).map ρ') ^ 2 - F.map ρ' :=
    map_dvd_sq_sub _ hd₁
  have hd₂z : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ'
      ∣ ((vτ.map PowerSeries.C).map ρ') ^ 2 - F.map ρ' := map_dvd_sq_sub _ hd₂
  have hd₃z : (phiU₃ a xQ).map ρ' ∣ ((phiV₃ xQ yQ m₀).map ρ') ^ 2 - F.map ρ' :=
    map_dvd_sq_sub _ hd₃
  -- certificate packs over `Kz` (glob side rewritten into phi-side spelling)
  have hcertsE := hcertsg.map E hu₁g hu₂g hu₃g
  rw [hFeq, map_globExpand_globConfig hbK hfaK hm hfa h2] at hcertsE
  have hcertsP := hcerts.map ρ' hu₁ hu₂ hu₃
  -- the `Fact` instances for the mapped `f` over `Kz`
  have hFz : (F.map ρ').natDegree = f.natDegree := by
    rw [(hf.map (PowerSeries.C : O →+* O⟦X⟧)).natDegree_map, hf.natDegree_map]
  have hOddKz : Fact (Odd ((F.map ρ').natDegree)) := ⟨by
    rw [hFz]
    have h := (Fact.out : Odd ((f.map ψ).natDegree))
    rwa [hf.natDegree_map] at h⟩
  have hSqKz : Fact (Squarefree (F.map ρ')) := ⟨by
    have hFχ : F.map ρ' = (f.map ψ).map
        ((algebraMap (PowerSeries K) Kz).comp (PowerSeries.C : K →+* K⟦X⟧)) := by
      rw [hFdef, Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext c
      simp [hρdef]
    rw [hFχ]
    exact ((PerfectField.separable_iff_squarefree.mpr Fact.out).map).squarefree⟩
  have hgz : 2 * uτ.natDegree < (F.map ρ').natDegree := by rw [hFz]; exact hgτ
  -- assemble: both pipelines have identical inputs, so certificate-independence applies
  rw [globPipeline, phiPipeline, hmapE, hmapP, hFeq, map_globExpand_globConfig hbK hfaK hm hfa h2]
  exact cantorPipeline_eq_cantorPipeline_of_mk0_eq hu₁z hd₁z hu₂z hd₂z hu₃z hd₃z
    hu₁z hd₁z hu₂z hd₂z hu₃z hd₃z hcertsE hcertsP hgz rfl

/-- **Disk-expansion transport for the chart coordinates**: the expansion of the global
chart coordinate `ζ_j` — a function on the curve — on the residue disk around `(a, b)` is
the per-disk chart coordinate series `phiZeta j`. -/
theorem globExpand_globZeta
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)) (hfaK : (f.map ψ).eval (ψ a) ≠ 0)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree) (j : Fin uτ.natDegree) :
    globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
        (globZeta (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
          ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d j)) := by
  have hpipe := map_globExpand_globPipeline dg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ huτ
    hdvdτ hgτ hcerts hcertsg
  injection hpipe with h1 h2
  rw [globZeta, map_chartCoords, phiZeta, map_chartCoords, map_chartCoords, chartCoords,
    chartCoords, h1]
  simp only [Polynomial.map_map]
  refine congrArg (fun φ ↦ Polynomial.coeff (_ - Polynomial.map φ uτ) _) (RingHom.ext fun c ↦ ?_)
  simp [globExpand_algebraMap_base, PowerSeries.map_C]

end Transport

section ChainRule

open HypField

variable {K : Type*} [Field K] {f : K[X]}

/-- Every function-field element decomposes as `g = re(g) + im(g)·y`. -/
theorem _root_.ChabautyColeman.HypField.eq_algebraMap_re_add_im (g : HypField K f) :
    g = algebraMap (RatFunc K) (HypField K f) g.re
      + algebraMap (RatFunc K) (HypField K f) g.im * y f := by
  ext <;> simp [QuadraticAlgebra.omega]

variable [NeZero (2 : K)] {a b : K} (hb : b ^ 2 = f.eval a) (hfa : f.eval a ≠ 0)

/-- Chain rule for the disk expansion on the rational-function part: expanding the
`x`-derivative is the `z`-derivative of the expansion (`x ↦ a + z` has slope `1`). -/
theorem globExpand_algebraMap_derivative (r : RatFunc K) :
    globExpand f a b hb hfa
        (algebraMap (RatFunc K) (HypField K f) (RatFunc.derivative r))
      = kzDeriv K (globExpand f a b hb hfa (algebraMap (RatFunc K) (HypField K f) r)) := by
  obtain ⟨p, q, hq, rfl⟩ := RatFunc.exists_eq_div r
  have hlift : ∀ s : K[X],
      IsFractionRing.lift (taylorFracHom_injective (K := K) a) (algebraMap K[X] (RatFunc K) s)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (taylor a s : K⟦X⟧) :=
    fun s ↦ IsFractionRing.lift_algebraMap _ s
  have htne : ∀ {s : K[X]}, s ≠ 0 → (taylor a s : K⟦X⟧) ≠ 0 := fun {s} hs h0 ↦ by
    refine hs (taylor_injective a ?_)
    rw [map_zero]
    exact_mod_cast h0
  have hnum : (taylor a (Polynomial.derivative p * q - p * Polynomial.derivative q) : K⟦X⟧)
      = (taylor a p.derivative : K⟦X⟧) * (taylor a q : K⟦X⟧)
        - (taylor a p : K⟦X⟧) * (taylor a q.derivative : K⟦X⟧) := by
    rw [map_sub, taylor_mul, taylor_mul]
    push_cast
    ring
  have hden : (taylor a (q ^ 2) : K⟦X⟧) = (taylor a q : K⟦X⟧) ^ 2 := by
    rw [taylor_pow]
    push_cast
    ring
  rw [RatFunc.derivative_div p hq, globExpand_algebraMap, globExpand_algebraMap, map_div₀,
    map_div₀, hlift, hlift, hlift, hlift,
    kzDeriv_div _ (htne hq),
    hnum, hden, PowerSeries.derivative_coe, PowerSeries.derivative_coe, derivative_taylor,
    derivative_taylor, map_sub, map_mul, map_mul, map_pow]

/-- Chain rule for the disk expansion at `y`: expanding `dy/dx = f′/(2f)·y` is the
`z`-derivative `b·η′` of the expansion `b·η` of `y`. -/
theorem globExpand_deriv_y (hf0 : f ≠ 0) :
    globExpand f a b hb hfa (HypField.deriv (y f))
      = kzDeriv K (globExpand f a b hb hfa (y f)) := by
  have hfa' : IsUnit (f.eval a) := isUnit_iff_ne_zero.mpr hfa
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
  have htne : ∀ {s : K[X]}, s ≠ 0 → (taylor a s : K⟦X⟧) ≠ 0 := fun {s} hs h0 ↦ by
    refine hs (taylor_injective a ?_)
    rw [map_zero]
    exact_mod_cast h0
  rw [deriv_y, map_mul, globExpand_algebraMap, globExpand_y, kzDeriv_algebraMap]
  rw [show PowerSeries.derivative (PowerSeries.C b * diskSeriesGeneric f a)
      = PowerSeries.C b * PowerSeries.derivative (diskSeriesGeneric f a) from by
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul]]
  have hlift : ∀ s : K[X],
      IsFractionRing.lift (taylorFracHom_injective (K := K) a) (algebraMap K[X] (RatFunc K) s)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (taylor a s : K⟦X⟧) :=
    fun s ↦ IsFractionRing.lift_algebraMap _ s
  rw [map_div₀, map_mul, map_ofNat, hlift, hlift]
  have h2ne : (2 : FractionRing (PowerSeries K)) ≠ 0 := by
    rw [← map_ofNat (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) 2]
    refine IsFractionRing.algebraMap_ne_zero fun h0 ↦ two_ne_zero (α := K) ?_
    have h1 := congrArg (PowerSeries.constantCoeff (R := K)) h0
    rwa [map_ofNat, map_zero] at h1
  have hfne : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (taylor a f : K⟦X⟧) ≠ 0 := IsFractionRing.algebraMap_ne_zero (htne hf0)
  rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h2ne hfne)]
  rw [show (2 : FractionRing (PowerSeries K))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) 2 from (map_ofNat _ 2).symm]
  simp only [← map_mul]
  refine congrArg _ ?_
  -- the `K⟦X⟧`-level identity, from the square-root chain rule and `η² = f(a+z)/f(a)`
  have h1 := two_mul_diskSeriesGeneric_mul_derivative hfa' h2
  have hsq : diskSeriesGeneric f a ^ 2 * PowerSeries.C (f.eval a) = (taylor a f : K⟦X⟧) := by
    rw [diskSeriesGeneric_sq hfa' h2, mul_assoc, ← map_mul,
      Ring.inverse_mul_cancel _ hfa', map_one, mul_one]
  linear_combination (2 * PowerSeries.C b * PowerSeries.derivative (diskSeriesGeneric f a))
      * hsq - (PowerSeries.C b * diskSeriesGeneric f a) * h1

/-- **Chain rule for the disk expansion**: expanding the curve derivative `D = d/dx` is the
`z`-derivative of the expansion (the chart is `x = a + z`). -/
theorem globExpand_deriv (hf0 : f ≠ 0) (g : HypField K f) :
    globExpand f a b hb hfa (HypField.deriv g)
      = kzDeriv K (globExpand f a b hb hfa g) := by
  have hdecomp := HypField.eq_algebraMap_re_add_im (f := f) g
  calc globExpand f a b hb hfa (HypField.deriv g)
      = globExpand f a b hb hfa (HypField.deriv (algebraMap (RatFunc K) (HypField K f) g.re
            + algebraMap (RatFunc K) (HypField K f) g.im * y f)) := by rw [← hdecomp]
    _ = kzDeriv K (globExpand f a b hb hfa (algebraMap (RatFunc K) (HypField K f) g.re
            + algebraMap (RatFunc K) (HypField K f) g.im * y f)) := by
        simp only [deriv_add, deriv_mul hf0, HypField.deriv_algebraMap, map_add, map_mul,
          kzDeriv_add, kzDeriv_mul, globExpand_algebraMap_derivative hb hfa,
          globExpand_deriv_y hb hfa hf0]
    _ = kzDeriv K (globExpand f a b hb hfa g) := by rw [← hdecomp]

end ChainRule

section OmegaTransport

open HypField

variable {O : Type*} [CommRing O] [Nontrivial O] {K : Type*} [Field K] [CharZero K]
  [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

/-- **The global differential numerator expands to `ω′`**: on the residue disk around
`(a, b)`, the expansion of `φ_i = y·∑_j N_{ij}·D(ζ_j)` is `b·η·ω′_i` — the per-disk
pullback series `ChabautyColeman.omegaPrime` times the expansion of `y`. The matrix `N`
enters through its defining property `hN` (its expansion is `M⁻¹ ∘ ζ`), and the coordinate
identification is `ChabautyColeman.globExpand_globZeta` combined with the chain rule
`ChabautyColeman.globExpand_deriv`. -/
theorem globExpand_globOmega
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)) (hfaK : (f.map ψ).eval (ψ a) ≠ 0)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree)
    (ΦK : FormalGroupLaw K (Fin (uτ.map ψ).natDegree))
    (ζK : Fin (uτ.map ψ).natDegree → K⟦X⟧)
    (hζK : ∀ j : Fin uτ.natDegree, ζK ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩
        = PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d j))
    (N : Fin (uτ.map ψ).natDegree → Fin (uτ.map ψ).natDegree → HypField K (f.map ψ))
    (hN : ∀ i j, globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (N i j)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (MvPowerSeries.subst ζK (ΦK.diffMatrix⁻¹ i j)))
    (i : Fin (uτ.map ψ).natDegree) :
    globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
        (globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg N i)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a) * omegaPrime ΦK ζK i) := by
  have hfK0 : f.map ψ ≠ 0 := (hf.map ψ).ne_zero
  -- the expansion of each chart-coordinate function is the coordinate series
  have hzeta : ∀ j : Fin (uτ.map ψ).natDegree,
      globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
          (globZeta (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg j)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (ζK j) := fun j ↦ by
    have hj : (j : ℕ) < uτ.natDegree := lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ)
    have h1 := globExpand_globZeta dg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ huτ hdvdτ hgτ
      hcerts hcertsg ⟨(j : ℕ), hj⟩
    have h2' := hζK ⟨(j : ℕ), hj⟩
    rw [show (⟨(j : ℕ), lt_of_lt_of_eq hj (huτ.natDegree_map ψ).symm⟩
        : Fin (uτ.map ψ).natDegree) = j from Fin.ext rfl] at h1 h2'
    rw [h1, h2']
  rw [globOmega, map_mul, globExpand_y, omegaPrime]
  simp only [map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hN i j, globExpand_deriv hbK hfaK hfK0, hzeta j, kzDeriv_algebraMap,
    pderiv_unit_eq_derivative]

/-- **The per-disk expansion identity from a regular numerator** (blueprint
`thm:omega-prime-global` clause (c), the second half of the assembly
`ChabautyColeman.omegaPrime_regular`): once the global differential numerator
`φ_i = y·∑_j N_{ij}·D(ζ_j)` is known to be a polynomial `P(x)`, the `ω′`-series times the
expansion `b·η` of `y` is the Taylor expansion of `P`, `b·η·ω′_i = P(a+z)`. Both sides are
expanded on the disk and compared through the injectivity of the expansion; how `P` was
obtained plays no role. -/
theorem omegaPrime_taylor
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)) (hfaK : (f.map ψ).eval (ψ a) ≠ 0)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree)
    (ΦK : FormalGroupLaw K (Fin (uτ.map ψ).natDegree))
    (ζK : Fin (uτ.map ψ).natDegree → K⟦X⟧)
    (hζK : ∀ j : Fin uτ.natDegree, ζK ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩
        = PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d j))
    (N : Fin (uτ.map ψ).natDegree → Fin (uτ.map ψ).natDegree → HypField K (f.map ψ))
    (hN : ∀ i j, globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (N i j)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (MvPowerSeries.subst ζK (ΦK.diffMatrix⁻¹ i j)))
    (i : Fin (uτ.map ψ).natDegree)
    {P : K[X]}
    (hPeq : globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg N i
      = HypRing.toHypField (f.map ψ) ⟨P, 0⟩) :
    PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a) * omegaPrime ΦK ζK i
      = (taylor (ψ a) P : K⟦X⟧) := by
  -- expand both sides of `hPeq` on the disk and compare series
  have h1 := globExpand_globOmega dg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ huτ hdvdτ hgτ
    hcerts hcertsg ΦK ζK hζK N hN i
  rw [hPeq, globExpand_toHypField] at h1
  have h2' : funcExpansionGeneric (f.map ψ)
      ((⟨P, 0⟩ : HypRing K (f.map ψ)).re) ((⟨P, 0⟩ : HypRing K (f.map ψ)).im) (ψ a) (ψ b)
      = (taylor (ψ a) P : K⟦X⟧) := by
    rw [funcExpansionGeneric]
    simp
  rw [h2'] at h1
  exact (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)) h1).symm

end OmegaTransport

end ChabautyColeman

end
