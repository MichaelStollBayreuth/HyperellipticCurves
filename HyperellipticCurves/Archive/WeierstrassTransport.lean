/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.DiskExpand
public import HyperellipticCurves.Archive.ForMathlib.QuadraticAlgebra
public import HyperellipticCurves.Curve.TraceMatrix
public import HyperellipticCurves.Log.Charts.WeierstrassChart

import HyperellipticCurves.ForMathlib.PowerSeries

/-!
# Weierstrass-disk expansion transport (the `hW`-identification at a Weierstrass centre)

The analogue of `HyperellipticCurves.Archive.DiskExpand` for a Weierstrass residue disk: the
expansion homomorphism sends `x ↦ W(z)` (the coordinate series with `f(W(z)) = z²`) and `y ↦ z` —
the disk parameter is the `y`-coordinate, so the chain rule carries the extra factor `W′(z)`. The
main theorems do not depend on this file.

* `ChabautyColeman.weierstrassExpand` — the expansion ring homomorphism `F_K →+* Frac(K⟦z⟧)`;
  injectivity on `K(x)` comes from `f(W) = z²` alone
  (`ChabautyColeman.aeval_eq_zero_iff_of_aeval_eq_X_sq`: a nonzero polynomial vanishing at
  `W` forces a linear minimal polynomial, i.e. `W` constant).
* `ChabautyColeman.map_weierstrassExpand_globPipeline` /
  `ChabautyColeman.weierstrassExpand_globZeta` —
  expanding the `(ω, 0)`-centred global pipeline yields the per-disk `w`-pipeline and its
  chart coordinates `wZeta`.
* `ChabautyColeman.kzDeriv_weierstrassExpand` — the chain rule: the `z`-derivative of the
  expansion is the expanded curve derivative times `W′`.
* `ChabautyColeman.X_mul_omegaPrime_eq_aeval_mul_derivative` — the taylor-form expansion
  identity `z·ω′_i = P(W(z))·W′(z)` for a polynomial global numerator `P`.
* `ChabautyColeman.map_omegaExpansionWeierstrass_eq_sum_smul_omegaPrime` — the
  `hW`-identification of `thm:disk-bound` at a Weierstrass centre, from the hypothesis
  `hPglob`: the `(ω, 0)`-centred global differential numerators are the trace-form
  numerators. This does **not** follow from the trace-form calculus directly — the centre
  pair block `[Q + ιP₀]` with `P₀ = (ω, 0)` contains a Weierstrass point, so the
  Θ-transfer along the second reduction step is genuinely singular there. The main
  development crosses the singular block with the extended calculus directly on the
  Weierstrass disk, without the function field
  (`HyperellipticCurves.Log.Trace.TraceKzWeierstrass`).

Blueprint nodes: `thm:omega-prime-global` (clause (c)), `thm:disk-bound`.
-/

@[expose] public section

open Polynomial
open scoped PowerSeries

namespace ChabautyColeman

section AevalInjective

variable {K : Type*} [Field K] {f : K[X]} {W : K⟦X⟧}

/-- A substitution point solving `f(W) = z²` is transcendental over the constants:
polynomial evaluation at `W` is injective on `K[X]`. If a nonzero polynomial vanished at
`W`, the minimal polynomial would; its constant-coefficient image forces the root `W(0)`
in `K`, making it linear and `W` constant — but then `f(W)` would be constant, not `z²`. -/
theorem aeval_eq_zero_iff_of_aeval_eq_X_sq (hWf : aeval W f = PowerSeries.X ^ 2)
    {p : K[X]} : aeval W p = 0 ↔ p = 0 := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ by rw [hp, map_zero]⟩
  by_contra hp0
  set w₀ := PowerSeries.constantCoeff W with hw₀
  -- `W` is not constant
  have hWne : W - PowerSeries.C w₀ ≠ 0 := by
    intro hc
    rw [sub_eq_zero] at hc
    have hfc : aeval W f = PowerSeries.C (f.eval w₀) := by
      rw [hc, show (PowerSeries.C w₀ : K⟦X⟧) = algebraMap K K⟦X⟧ w₀ from rfl,
        aeval_algebraMap_apply]
      simp
    have h2 := congrArg (PowerSeries.coeff 2) (hWf.symm.trans hfc)
    rw [PowerSeries.coeff_X_pow, ite_eq_left rfl, PowerSeries.coeff_C] at h2
    simp at h2
  -- the minimal polynomial has the root `W(0)`, hence is linear
  have hint : IsIntegral K W := (IsAlgebraic.isIntegral ⟨p, hp0, hp⟩)
  have hroot : (minpoly K W).eval w₀ = 0 := by
    have h := congrArg PowerSeries.constantCoeff (minpoly.aeval K W)
    rwa [PowerSeries.constantCoeff_aeval, map_zero] at h
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hroot
  rcases (minpoly.irreducible hint).isUnit_or_isUnit hr with hu | hu
  · exact not_isUnit_X_sub_C w₀ hu
  · obtain ⟨u, huu, hru⟩ := Polynomial.isUnit_iff.mp hu
    have h0 := minpoly.aeval K W
    rw [hr, ← hru, map_mul, map_sub, aeval_X, aeval_C, aeval_C] at h0
    have hCu : (algebraMap K K⟦X⟧) u ≠ 0 := fun h ↦ huu.ne_zero (by
      have := congrArg PowerSeries.constantCoeff h
      simpa using this)
    exact hWne ((mul_eq_zero.mp h0).resolve_right hCu)

end AevalInjective

section WeierstrassExpandHom

open HypField

variable {K : Type*} [Field K]

/-- The composite `K[X] → K⟦z⟧ → Frac(K⟦z⟧)`, evaluation at the coordinate series `W`
followed by the inclusion into the fraction field. -/
noncomputable def aevalFracHom (W : K⟦X⟧) : K[X] →+* FractionRing (PowerSeries K) :=
  (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (aeval W).toRingHom

theorem aevalFracHom_apply (W : K⟦X⟧) (p : K[X]) :
    aevalFracHom W p
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (aeval W p) := rfl

theorem aevalFracHom_injective {f : K[X]} {W : K⟦X⟧}
    (hWf : aeval W f = PowerSeries.X ^ 2) : Function.Injective (aevalFracHom W) := by
  intro p q h
  have h1 : aeval W p = aeval W q := IsFractionRing.injective (PowerSeries K) _ h
  exact sub_eq_zero.mp ((aeval_eq_zero_iff_of_aeval_eq_X_sq hWf).mp (by rw [map_sub, h1, sub_self]))

variable {f : K[X]} {W : K⟦X⟧}

/-- The square-root certificate for the Weierstrass-disk expansion: the disk parameter `z`
squares to the image of the defining coefficient `f` of the function field. -/
theorem sq_algebraMap_X_of_aeval (hWf : aeval W f = PowerSeries.X ^ 2) :
    algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ 2
      = IsFractionRing.lift (aevalFracHom_injective hWf) (algebraMap K[X] (RatFunc K) f)
        + IsFractionRing.lift (aevalFracHom_injective hWf) (0 : RatFunc K)
          * algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X := by
  rw [map_zero, zero_mul, add_zero, IsFractionRing.lift_algebraMap, aevalFracHom_apply,
    ← map_pow, ← hWf]

/-- **The Weierstrass-disk expansion homomorphism on the function field**: the ring
homomorphism `F_K →+* Frac(K⟦z⟧)` expanding a curve function on the residue disk around a
Weierstrass point: `x ↦ W(z)` for a coordinate series `W` with `f(W(z)) = z²`, and
`y ↦ z` — the disk parameter is the `y`-coordinate. The analogue at a Weierstrass centre
of `ChabautyColeman.globExpand`. -/
noncomputable def weierstrassExpand (f : K[X]) (W : K⟦X⟧)
    (hWf : aeval W f = PowerSeries.X ^ 2) :
    HypField K f →+* FractionRing (PowerSeries K) :=
  QuadraticAlgebra.liftRingHom (IsFractionRing.lift (aevalFracHom_injective hWf))
    (algebraMap (PowerSeries K) _ PowerSeries.X) (sq_algebraMap_X_of_aeval hWf)

variable (hWf : aeval W f = PowerSeries.X ^ 2)

theorem weierstrassExpand_algebraMap (r : RatFunc K) :
    weierstrassExpand f W hWf (algebraMap (RatFunc K) (HypField K f) r)
      = IsFractionRing.lift (aevalFracHom_injective hWf) r :=
  RingHom.congr_fun (QuadraticAlgebra.liftRingHom_comp_algebraMap _ _
    (sq_algebraMap_X_of_aeval hWf)) r

theorem weierstrassExpand_algebraMap_polynomial (p : K[X]) :
    weierstrassExpand f W hWf (algebraMap K[X] (HypField K f) p)
      = algebraMap (PowerSeries K) _ (aeval W p) := by
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f), weierstrassExpand_algebraMap,
    IsFractionRing.lift_algebraMap]
  rfl

theorem weierstrassExpand_algebraMap_base (c : K) :
    weierstrassExpand f W hWf (algebraMap K (HypField K f) c)
      = algebraMap (PowerSeries K) _ (PowerSeries.C c) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (HypField K f), weierstrassExpand_algebraMap_polynomial,
    Polynomial.algebraMap_eq, aeval_C]
  rfl

theorem weierstrassExpand_x :
    weierstrassExpand f W hWf (x f) = algebraMap (PowerSeries K) _ W := by
  rw [x, weierstrassExpand_algebraMap_polynomial, aeval_X]

theorem weierstrassExpand_y :
    weierstrassExpand f W hWf (y f) = algebraMap (PowerSeries K) _ PowerSeries.X :=
  QuadraticAlgebra.liftRingHom_omega _ _ (sq_algebraMap_X_of_aeval hWf)

/-- On the coordinate ring, the Weierstrass-disk expansion is the componentwise evaluation
at the coordinate series. -/
theorem weierstrassExpand_toHypField (w : HypRing K f) :
    weierstrassExpand f W hWf (HypRing.toHypField f w)
      = algebraMap (PowerSeries K) _ (aeval W w.re + aeval W w.im * PowerSeries.X) := by
  rw [HypRing.toHypField_apply, map_add, map_mul, weierstrassExpand_algebraMap_polynomial,
    weierstrassExpand_algebraMap_polynomial, weierstrassExpand_y, map_add, map_mul]

end WeierstrassExpandHom

section WeierstrassBlockTransport

open HypField

variable {O : Type*} [CommRing O] {K : Type*} [Field K] {ψ : O →+* K}
  {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0)
  (hωu : IsUnit (f.derivative.eval ω)) {xQ yQ m₀ : O} {m : O⟦X⟧}

/-- The mapped coordinate series still solves `f(W) = z²`. -/
theorem aeval_map_weierstrassSeries :
    aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) (f.map ψ)
      = PowerSeries.X ^ 2 := by
  have h := congrArg (PowerSeries.map ψ) (weierstrassSeries_eval hf hdeg hω hωu)
  rw [map_pow, PowerSeries.map_X] at h
  rw [← h, aeval_def, aeval_def, eval₂_map, Polynomial.hom_eval₂]
  congr 1
  ext c
  simp

/-- The two transports agree on the base ring: expanding a global constant gives the
constant series. -/
theorem weierstrassExpand_algebraMap_base_comp (c : O) :
    weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu)
        (algebraMap K (HypField K (f.map ψ)) (ψ c))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) (PowerSeries.C c) := by
  rw [weierstrassExpand_algebraMap_base, RingHom.comp_apply, PowerSeries.map_C]

/-- **Transport of a constant block**: a global datum with coefficients in the base expands
to the constant-series datum. -/
theorem map_weierstrassExpand_map_algebraMap (p : O[X]) :
    ((p.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map
        (weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (aeval_map_weierstrassSeries hf hdeg hω hωu))
      = (p.map (PowerSeries.C : O →+* O⟦X⟧)).map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
            (PowerSeries.map ψ)) := by
  simp only [Polynomial.map_map]
  exact congrArg (Polynomial.map · p)
    (RingHom.ext (weierstrassExpand_algebraMap_base_comp hf hdeg hω hωu))

/-- The coordinate `x` expands to the Weierstrass coordinate series. -/
theorem weierstrassExpand_x_eq_weierstrassSeries :
    weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu) (HypField.x (f.map ψ))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) (weierstrassSeries hf hdeg hω hωu) := by
  rw [weierstrassExpand_x, RingHom.comp_apply]

/-- The coordinate `y` expands to the disk parameter. -/
theorem weierstrassExpand_y_eq_X :
    weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu) (HypField.y (f.map ψ))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) PowerSeries.X := by
  rw [weierstrassExpand_y, RingHom.comp_apply, PowerSeries.map_X]

/-- **Transport of the constant pair block**, `u`-part. -/
theorem map_weierstrassExpand_globU₃ :
    (globU₃ (f.map ψ) (ψ ω) (ψ xQ)).map (weierstrassExpand (f.map ψ)
        (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu))
      = (phiU₃ ω xQ).map ((algebraMap (PowerSeries K)
          (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)) := by
  rw [globU₃, phiU₃,
    show ((X - C (ψ xQ)) * (X - C (ψ ω)) : K[X]) = ((X - C xQ) * (X - C ω)).map ψ by simp,
    ← map_weierstrassExpand_map_algebraMap hf hdeg hω hωu ((X - C xQ) * (X - C ω))]

/-- **Transport of the constant pair block**, `v`-part. -/
theorem map_weierstrassExpand_globV₃ :
    (globV₃ (f.map ψ) (ψ xQ) (ψ yQ) (ψ m₀)).map (weierstrassExpand (f.map ψ)
        (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu))
      = (phiV₃ xQ yQ m₀).map ((algebraMap (PowerSeries K)
          (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)) := by
  rw [globV₃, phiV₃, ← pairV_map,
    ← map_weierstrassExpand_map_algebraMap hf hdeg hω hωu (pairV xQ yQ m₀)]

variable [Fact (Odd (f.map ψ).natDegree)]

/-- The global slope of the moving pair expands to the Weierstrass disk slope certificate. -/
theorem weierstrassExpand_globSlope_eq (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X) :
    weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu) (globSlope (f.map ψ) (ψ xQ) (ψ yQ))
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)) m := by
  set ρ' : O⟦X⟧ →+* FractionRing (PowerSeries K)
    := (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
      (PowerSeries.map ψ) with hρdef
  have hDne : ρ' (PowerSeries.C xQ) - ρ' (weierstrassSeries hf hdeg hω hωu) ≠ 0 := by
    rw [← map_sub, hρdef, RingHom.comp_apply]
    refine (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)).mpr fun h0 ↦ ?_
    have h1 := congrArg (PowerSeries.coeff (0 : ℕ)) h0
    rw [map_zero, map_sub, map_sub, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_C,
      constantCoeff_weierstrassSeries] at h1
    have hu := hsep.map ψ
    rw [map_sub, h1] at hu
    exact not_isUnit_zero hu
  have h1 := congrArg (weierstrassExpand (f.map ψ)
    (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
    (aeval_map_weierstrassSeries hf hdeg hω hωu)) (globSlope_spec (f.map ψ) (ψ xQ) (ψ yQ))
  rw [map_mul, map_sub, map_sub, weierstrassExpand_algebraMap_base_comp hf hdeg hω hωu xQ,
    weierstrassExpand_x_eq_weierstrassSeries hf hdeg hω hωu, ← map_neg ψ yQ,
    weierstrassExpand_algebraMap_base_comp hf hdeg hω hωu (-yQ),
    weierstrassExpand_y_eq_X hf hdeg hω hωu] at h1
  have h2' := congrArg ρ' hm
  rw [map_mul, map_sub, map_sub] at h2'
  exact mul_right_cancel₀ hDne (h1.trans h2'.symm)

/-- **Transport of the moving pair block**, `u`-part. -/
theorem map_weierstrassExpand_globU₁ :
    (globU₁ (f.map ψ) (ψ xQ)).map (weierstrassExpand (f.map ψ)
        (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu))
      = (wU₁ hf hdeg hω hωu xQ).map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
            (PowerSeries.map ψ)) := by
  simp only [globU₁, wU₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, weierstrassExpand_x_eq_weierstrassSeries hf hdeg hω hωu,
    weierstrassExpand_algebraMap_base_comp hf hdeg hω hωu xQ, RingHom.comp_apply,
    PowerSeries.map_C]

/-- **Transport of the moving pair block**, `v`-part. -/
theorem map_weierstrassExpand_globV₁ (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X) :
    (globV₁ (f.map ψ) (ψ xQ) (ψ yQ)).map (weierstrassExpand (f.map ψ)
        (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu))
      = (wV₁ hf hdeg hω hωu m).map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
            (PowerSeries.map ψ)) := by
  rw [globV₁, wV₁, pairV_map, pairV_map, weierstrassExpand_x_eq_weierstrassSeries hf hdeg hω hωu,
    weierstrassExpand_y_eq_X hf hdeg hω hωu, weierstrassExpand_globSlope_eq hf hdeg hω hωu hsep hm]

/-- **The global three-block configuration expands to the Weierstrass per-disk one**: the
six blockwise identifications above, as one equation between configurations. -/
theorem map_weierstrassExpand_globConfig {uτ vτ : O[X]} (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X) :
    (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀)).map
        (weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (aeval_map_weierstrassSeries hf hdeg hω hωu))
      = (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ).map
        ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)) :=
  PipelineData.map_eq_of_blocks (map_weierstrassExpand_globU₁ hf hdeg hω hωu)
    (map_weierstrassExpand_globV₁ hf hdeg hω hωu hsep hm)
    (map_weierstrassExpand_map_algebraMap hf hdeg hω hωu uτ)
    (map_weierstrassExpand_map_algebraMap hf hdeg hω hωu vτ)
    (map_weierstrassExpand_globU₃ hf hdeg hω hωu) (map_weierstrassExpand_globV₃ hf hdeg hω hωu)

end WeierstrassBlockTransport

section WeierstrassTransport

open HypField

variable {O : Type*} [CommRing O] [Nontrivial O] {K : Type*} [Field K] [CharZero K]
  {ψ : O →+* K}
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

/-- **Weierstrass-disk expansion transport for the chart pipeline**: expanding the
`(ω, 0)`-centred global pipeline on the Weierstrass residue disk yields exactly the
per-disk `w`-pipeline. The analogue of `ChabautyColeman.map_globExpand_globPipeline`; both
sides are compared inside `Frac(K⟦z⟧)` and agree by uniqueness of reduced
representatives. -/
theorem map_weierstrassExpand_globPipeline
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree) :
    ((globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg).1.map
        (weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (aeval_map_weierstrassSeries hf hdeg hω hωu)),
      (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg).2.map
        (weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (aeval_map_weierstrassSeries hf hdeg hω hωu)))
      = ((wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)),
        (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2.map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
            (PowerSeries.map ψ))) := by
  classical
  -- the seven input identifications: `E` on the global data is `ρ'` on the disk data
  have hFeq := map_weierstrassExpand_map_algebraMap (ψ := ψ) hf hdeg hω hωu f
  have hDeq := map_weierstrassExpand_globConfig (ψ := ψ) (xQ := xQ) (yQ := yQ) (m₀ := m₀)
    (uτ := uτ) (vτ := vτ) hf hdeg hω hωu hsep hm
  set Kz := FractionRing (PowerSeries K) with hKzdef
  set E := weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
    (aeval_map_weierstrassSeries hf hdeg hω hωu) with hEdef
  set ρ' : O⟦X⟧ →+* Kz
    := (algebraMap (PowerSeries K) Kz).comp (PowerSeries.map ψ) with hρdef
  -- ambient facts over `Kz`
  have hinj : Function.Injective (algebraMap (PowerSeries K) Kz) :=
    IsFractionRing.injective (PowerSeries K) Kz
  have hchPS : CharZero (PowerSeries K) := (PowerSeries.constantCoeff : K⟦X⟧ →+* K).charZero
  have hchKz : CharZero Kz := charZero_of_injective_algebraMap hinj
  have h2Kz : NeZero (2 : Kz) := ⟨by norm_num⟩
  -- the disk-side input facts over `O⟦X⟧`
  set F : (O⟦X⟧)[X] := f.map PowerSeries.C with hFdef
  have hu₁ : (wU₁ hf hdeg hω hωu xQ).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hu₃ : (phiU₃ ω xQ (O := O)).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₁ : wU₁ hf hdeg hω hωu xQ ∣ wV₁ hf hdeg hω hωu m ^ 2 - F :=
    movingPair_dvd_weierstrass hf hdeg hω hωu hsep hm hyQ
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧) ∣ (vτ.map PowerSeries.C) ^ 2 - F :=
    map_dvd_sq_sub _ hdvdτ
  have hsepn : IsUnit (ω - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hd₃ : phiU₃ ω xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - F :=
    map_dvd_sq_sub _ (pair_dvd hsepn hm₀ hyQ
      (by rw [neg_zero, zero_pow two_ne_zero]; exact hω.symm))
  -- the glob-side input facts over the function field
  have hyQK : (ψ yQ) ^ 2 = (f.map ψ).eval (ψ xQ) := map_sq_eq_eval_map ψ hyQ
  have hsepK : ψ ω ≠ ψ xQ := map_ne_of_isUnit_sub ψ hsep
  have hm₀K : (ψ m₀) * (ψ ω - ψ xQ) = -(0 : K) - ψ yQ := by
    rw [← map_sub, ← map_mul, hm₀, map_sub, map_neg, map_zero]
  have hbK0 : (0 : K) ^ 2 = (f.map ψ).eval (ψ ω) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hω, map_zero, zero_pow two_ne_zero]
  have hu₁g : (globU₁ (f.map ψ) (ψ xQ)).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂g : ((uτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))).Monic :=
    (huτ.map ψ).map _
  have hu₃g : (globU₃ (f.map ψ) (ψ ω) (ψ xQ)).Monic :=
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hdvdτK : uτ.map ψ ∣ (vτ.map ψ) ^ 2 - f.map ψ :=
    map_dvd_sq_sub ψ hdvdτ
  have hd₁g := globPair_dvd (f.map ψ) hyQK
  have hd₂g : (uτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))
      ∣ ((vτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))) ^ 2
        - (f.map ψ).map (algebraMap K (HypField K (f.map ψ))) :=
    map_dvd_sq_sub _ hdvdτK
  have hd₃g := globPair₃_dvd (f.map ψ) hsepK hm₀K hbK0 hyQK
  -- pipelines mapped into `Kz`
  have hmapE := map_cantorPipeline_generic E hu₁g hu₂g hu₃g hcertsg
  have hmapP := map_cantorPipeline_generic ρ' hu₁ hu₂ hu₃ hcerts
  -- monic/dvd facts for the common inputs over `Kz`, disk-side spelling
  have hu₁z : ((wU₁ hf hdeg hω hωu xQ).map ρ').Monic := hu₁.map ρ'
  have hu₂z : ((uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ').Monic := hu₂.map ρ'
  have hu₃z : ((phiU₃ ω xQ).map ρ').Monic := hu₃.map ρ'
  have hd₁z : (wU₁ hf hdeg hω hωu xQ).map ρ'
      ∣ ((wV₁ hf hdeg hω hωu m).map ρ') ^ 2 - F.map ρ' := map_dvd_sq_sub _ hd₁
  have hd₂z : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ'
      ∣ ((vτ.map PowerSeries.C).map ρ') ^ 2 - F.map ρ' := map_dvd_sq_sub _ hd₂
  have hd₃z : (phiU₃ ω xQ).map ρ' ∣ ((phiV₃ xQ yQ m₀).map ρ') ^ 2 - F.map ρ' :=
    map_dvd_sq_sub _ hd₃
  -- certificate packs over `Kz` (glob side rewritten into disk-side spelling)
  have hcertsE := hcertsg.map E hu₁g hu₂g hu₃g
  rw [hFeq, hDeq] at hcertsE
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
  rw [globPipeline, wPipeline, hmapE, hmapP, hFeq, hDeq]
  exact cantorPipeline_eq_cantorPipeline_of_mk0_eq hu₁z hd₁z hu₂z hd₂z hu₃z hd₃z
    hu₁z hd₁z hu₂z hd₂z hu₃z hd₃z hcertsE hcertsP hgz rfl

/-- **Weierstrass-disk expansion transport for the chart coordinates**: the expansion of
the `(ω, 0)`-centred global chart coordinate `ζ_j` on the Weierstrass disk is the per-disk
chart coordinate series `wZeta j`. The analogue of
`ChabautyColeman.globExpand_globZeta`. -/
theorem weierstrassExpand_globZeta
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree) (j : Fin uτ.natDegree) :
    weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu)
        (globZeta (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg
          ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j)) := by
  have hpipe := map_weierstrassExpand_globPipeline dg hf hdeg hω hωu hsep hm hm₀ hyQ huτ
    hdvdτ hgτ hcerts hcertsg
  injection hpipe with h1 h2
  rw [globZeta, map_chartCoords, wZeta, map_chartCoords, map_chartCoords, chartCoords,
    chartCoords, h1]
  simp only [Polynomial.map_map]
  refine congrArg (fun φ ↦ Polynomial.coeff (_ - Polynomial.map φ uτ) _) (RingHom.ext fun c ↦ ?_)
  simp [weierstrassExpand_algebraMap_base, PowerSeries.map_C]

end WeierstrassTransport

section WeierstrassChainRule

open HypField

variable {K : Type*} [Field K] {f : K[X]} {W : K⟦X⟧}

/-- The power-series chain rule for polynomial evaluation:
`d/dz p(W(z)) = p′(W(z))·W′(z)`. -/
theorem derivative_aeval (W : K⟦X⟧) (p : K[X]) :
    PowerSeries.derivative (aeval W p)
      = aeval W (Polynomial.derivative p) * PowerSeries.derivative W := by
  have h := Derivation.comp_aeval_eq (PowerSeries.derivative) p (a := W)
  rwa [smul_eq_mul] at h

variable (hWf : aeval W f = PowerSeries.X ^ 2)

/-- Chain rule for the Weierstrass-disk expansion on the rational-function part: the
`z`-derivative of the expansion is the expanded `x`-derivative times `W′` (the chart is
`x = W(z)`). -/
theorem kzDeriv_weierstrassExpand_algebraMap (r : RatFunc K) :
    kzDeriv K (weierstrassExpand f W hWf (algebraMap (RatFunc K) (HypField K f) r))
      = weierstrassExpand f W hWf (algebraMap (RatFunc K) (HypField K f) (RatFunc.derivative r))
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (PowerSeries.derivative W) := by
  obtain ⟨p, q, hq, rfl⟩ := RatFunc.exists_eq_div r
  have hlift : ∀ s : K[X],
      IsFractionRing.lift (aevalFracHom_injective hWf) (algebraMap K[X] (RatFunc K) s)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (aeval W s) :=
    fun s ↦ IsFractionRing.lift_algebraMap _ s
  have hane : ∀ {s : K[X]}, s ≠ 0 → aeval W s ≠ 0 := fun {s} hs h0 ↦
    hs ((aeval_eq_zero_iff_of_aeval_eq_X_sq hWf).mp h0)
  have hnum : aeval W (Polynomial.derivative p * q - p * Polynomial.derivative q)
      = aeval W (Polynomial.derivative p) * aeval W q
        - aeval W p * aeval W (Polynomial.derivative q) := by
    rw [map_sub, map_mul, map_mul]
  rw [RatFunc.derivative_div p hq, weierstrassExpand_algebraMap, weierstrassExpand_algebraMap,
    map_div₀, map_div₀, hlift, hlift, hlift, hlift, kzDeriv_div _ (hane hq),
    derivative_aeval, derivative_aeval, div_mul_eq_mul_div]
  congr 1
  · simp only [← map_mul, ← map_sub]
    exact congrArg _ (by rw [hnum]; ring)
  · exact congrArg _ (map_pow (aeval W) q 2).symm

variable [NeZero (2 : K)]

/-- Chain rule for the Weierstrass-disk expansion at `y`: the `z`-derivative of the
expansion `z` of `y` (namely `1`) is the expanded `dy/dx = f′/(2f)·y` times `W′` — the
chain-rule identity `f′(W)·W′ = 2z`. -/
theorem kzDeriv_weierstrassExpand_y (hf0 : f ≠ 0) :
    kzDeriv K (weierstrassExpand f W hWf (y f))
      = weierstrassExpand f W hWf (HypField.deriv (y f))
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (PowerSeries.derivative W) := by
  have hlift : ∀ s : K[X],
      IsFractionRing.lift (aevalFracHom_injective hWf) (algebraMap K[X] (RatFunc K) s)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (aeval W s) :=
    fun s ↦ IsFractionRing.lift_algebraMap _ s
  have hane : ∀ {s : K[X]}, s ≠ 0 → aeval W s ≠ 0 := fun {s} hs h0 ↦
    hs ((aeval_eq_zero_iff_of_aeval_eq_X_sq hWf).mp h0)
  have hchain : aeval W (Polynomial.derivative f) * PowerSeries.derivative W
      = 2 * PowerSeries.X := by
    have hc := Derivation.comp_aeval_eq (PowerSeries.derivative) f (a := W)
    rw [hWf, smul_eq_mul] at hc
    rw [← hc, PowerSeries.derivative_pow, PowerSeries.derivative_X]
    simp
  rw [weierstrassExpand_y, kzDeriv_algebraMap, PowerSeries.derivative_X, map_one, deriv_y,
    map_mul, weierstrassExpand_algebraMap, weierstrassExpand_y, map_div₀, map_mul, map_ofNat, hlift,
    hlift]
  have h2ne : (2 : FractionRing (PowerSeries K)) ≠ 0 := by
    rw [← map_ofNat (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) 2]
    refine IsFractionRing.algebraMap_ne_zero fun h0 ↦ ?_
    have h1 := congrArg (PowerSeries.constantCoeff (R := K)) h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero h1
  have hfne : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (aeval W f) ≠ 0 :=
    IsFractionRing.algebraMap_ne_zero (hane hf0)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_comm, div_eq_one_iff_eq (mul_ne_zero h2ne hfne)]
  rw [show (2 : FractionRing (PowerSeries K))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) 2 from (map_ofNat _ 2).symm]
  simp only [← map_mul]
  refine congrArg _ ?_
  rw [hWf]
  linear_combination PowerSeries.X * hchain

/-- **Chain rule for the Weierstrass-disk expansion**: the `z`-derivative of the expansion
is the expanded curve derivative `D = d/dx` times `W′` — the chart is `x = W(z)`. -/
theorem kzDeriv_weierstrassExpand (hf0 : f ≠ 0) (g : HypField K f) :
    kzDeriv K (weierstrassExpand f W hWf g)
      = weierstrassExpand f W hWf (HypField.deriv g)
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (PowerSeries.derivative W) := by
  have hdecomp := HypField.eq_algebraMap_re_add_im (f := f) g
  calc kzDeriv K (weierstrassExpand f W hWf g)
      = kzDeriv K (weierstrassExpand f W hWf (algebraMap (RatFunc K) (HypField K f) g.re
          + algebraMap (RatFunc K) (HypField K f) g.im * y f)) := by rw [← hdecomp]
    _ = weierstrassExpand f W hWf (HypField.deriv (algebraMap (RatFunc K) (HypField K f) g.re
          + algebraMap (RatFunc K) (HypField K f) g.im * y f))
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (PowerSeries.derivative W) := by
        simp only [deriv_add, deriv_mul hf0, HypField.deriv_algebraMap, map_add, map_mul,
          kzDeriv_add, kzDeriv_mul, kzDeriv_weierstrassExpand_algebraMap hWf,
          kzDeriv_weierstrassExpand_y hWf hf0]
        ring
    _ = weierstrassExpand f W hWf (HypField.deriv g)
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (PowerSeries.derivative W) := by rw [← hdecomp]

end WeierstrassChainRule

section WeierstrassOmegaTransport

open HypField

variable {O : Type*} [CommRing O] [Nontrivial O] {K : Type*} [Field K] [CharZero K]
  [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

/-- **The global differential numerator expands to `ω′` on the Weierstrass disk**: with
the chart `x = W(z)`, `y = z`, the expansion of `φ_i = y·∑_j N_{ij}·D(ζ_j)` times `W′` is
`z·ω′_i` — the per-disk pullback series along the Weierstrass chart coordinates `wZeta`.
The analogue of `ChabautyColeman.globExpand_globOmega`; the factor `W′` is the chain-rule
slope of the chart. -/
theorem weierstrassExpand_globOmega
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree)
    (ΦK : FormalGroupLaw K (Fin (uτ.map ψ).natDegree))
    (ζK : Fin (uτ.map ψ).natDegree → K⟦X⟧)
    (hζK : ∀ j : Fin uτ.natDegree, ζK ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩
        = PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j))
    (N : Fin (uτ.map ψ).natDegree → Fin (uτ.map ψ).natDegree → HypField K (f.map ψ))
    (hN : ∀ i j, weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu) (N i j)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (MvPowerSeries.subst ζK (ΦK.diffMatrix⁻¹ i j)))
    (i : Fin (uτ.map ψ).natDegree) :
    weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu)
        (globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg N i)
      * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.X * omegaPrime ΦK ζK i) := by
  have hfK0 : f.map ψ ≠ 0 := (hf.map ψ).ne_zero
  have hzeta : ∀ j : Fin (uτ.map ψ).natDegree,
      weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (aeval_map_weierstrassSeries hf hdeg hω hωu)
          (globZeta (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg j)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (ζK j) := fun j ↦ by
    have hj : (j : ℕ) < uτ.natDegree := lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ)
    have h1 := weierstrassExpand_globZeta dg hf hdeg hω hωu hsep hm hm₀ hyQ huτ hdvdτ hgτ
      hcerts hcertsg ⟨(j : ℕ), hj⟩
    have h2' := hζK ⟨(j : ℕ), hj⟩
    rw [show (⟨(j : ℕ), lt_of_lt_of_eq hj (huτ.natDegree_map ψ).symm⟩
        : Fin (uτ.map ψ).natDegree) = j from Fin.ext rfl] at h1 h2'
    rw [h1, h2']
  calc weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu)
        (globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg N i)
      * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X
        * ∑ j, algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (MvPowerSeries.subst ζK (ΦK.diffMatrix⁻¹ i j))
          * (weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
              (aeval_map_weierstrassSeries hf hdeg hω hωu)
              (HypField.deriv
                (globZeta (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg j))
            * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
                (PowerSeries.derivative
                  (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)))) := by
        rw [globOmega, map_mul, weierstrassExpand_y, map_sum, mul_assoc, Finset.sum_mul]
        refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
        rw [map_mul, hN i j, mul_assoc]
    _ = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.X * omegaPrime ΦK ζK i) := by
        rw [omegaPrime, map_mul, map_sum]
        refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
        rw [← kzDeriv_weierstrassExpand _ hfK0, hzeta j, kzDeriv_algebraMap,
          pderiv_unit_eq_derivative, map_mul]

/-- **The taylor-form expansion identity at a Weierstrass centre**: if the global
differential numerator `φ_i` is a polynomial `P` in `x`, then on the Weierstrass disk
`z·ω′_i = P(W(z))·W′(z)` — the identity feeding the `hW`-slot of the per-disk bound, with
`P = tracePoly i`. The analogue of `ChabautyColeman.omegaPrime_taylor`. -/
theorem X_mul_omegaPrime_eq_aeval_mul_derivative
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree)
    (ΦK : FormalGroupLaw K (Fin (uτ.map ψ).natDegree))
    (ζK : Fin (uτ.map ψ).natDegree → K⟦X⟧)
    (hζK : ∀ j : Fin uτ.natDegree, ζK ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩
        = PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j))
    (N : Fin (uτ.map ψ).natDegree → Fin (uτ.map ψ).natDegree → HypField K (f.map ψ))
    (hN : ∀ i j, weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu) (N i j)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (MvPowerSeries.subst ζK (ΦK.diffMatrix⁻¹ i j)))
    (i : Fin (uτ.map ψ).natDegree)
    {P : K[X]}
    (hPeq : globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg N i
      = HypRing.toHypField (f.map ψ) ⟨P, 0⟩) :
    PowerSeries.X * omegaPrime ΦK ζK i
      = aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) P
        * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) := by
  have h1 := weierstrassExpand_globOmega dg hf hdeg hω hωu hsep hm hm₀ hyQ huτ hdvdτ hgτ hcerts
    hcertsg ΦK ζK hζK N hN i
  rw [hPeq, weierstrassExpand_toHypField] at h1
  simp only [map_zero, zero_mul, add_zero, ← map_mul] at h1
  exact (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)) h1).symm

end WeierstrassOmegaTransport

section WeierstrassCapstone

open HypField

variable {O : Type*} [CommRing O] [Nontrivial O] {K : Type*} [Field K] [CharZero K]
  [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ c₂ : O[X]} {d : CantorCertData O⟦X⟧}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

/-- **The `hW`-identification at a Weierstrass centre** (blueprint `thm:disk-bound`, the
Weierstrass case): if the numerator `h₀` has coordinates `cs` in the trace-form basis, then
the integral disk expansion of `h₀·dx/y` at the Weierstrass centre `(ω, 0)` is
`∑_i cs_i·ω′_i` for the Weierstrass chart coordinates `wZeta` of that disk.

The input `hPglob` — the `(ω, 0)`-centred global differential numerators are the
trace-form numerators — does not follow from the trace-form calculus directly, unlike at a
generic centre (where the per-disk calculus of `HyperellipticCurves.Log.Trace.TraceKz` applies): the
centre pair block `[Q + ιP₀]` with `P₀ = (ω, 0)` contains a Weierstrass point, so the
Θ-transfer along the second reduction step is genuinely singular there. It is passed as a
hypothesis here; the main development proves the per-disk counterpart directly
(`HyperellipticCurves.Log.Trace.TraceKzWeierstrass`), crossing the singular block with the
extended Θ-calculus. -/
theorem map_omegaExpansionWeierstrass_eq_sum_smul_omegaPrime
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree)
    (ΦK : FormalGroupLaw K (Fin (uτ.map ψ).natDegree))
    (ζK : Fin (uτ.map ψ).natDegree → K⟦X⟧)
    (hζK : ∀ j : Fin uτ.natDegree, ζK ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩
        = PowerSeries.map ψ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j))
    (N : Fin (uτ.map ψ).natDegree → Fin (uτ.map ψ).natDegree → HypField K (f.map ψ))
    (hN : ∀ i j, weierstrassExpand (f.map ψ) (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
        (aeval_map_weierstrassSeries hf hdeg hω hωu) (N i j)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (MvPowerSeries.subst ζK (ΦK.diffMatrix⁻¹ i j)))
    (hPglob : ∀ i, globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ ω) (ψ xQ) (ψ yQ) (ψ m₀) dg N i
      = HypRing.toHypField (f.map ψ) ⟨tracePoly (uτ.map ψ) (c₂.map ψ) i, 0⟩)
    {cs : Fin (uτ.map ψ).natDegree → K} {h₀ : O[X]}
    (hmap : h₀.map ψ = ∑ i, cs i • tracePoly (uτ.map ψ) (c₂.map ψ) i) :
    PowerSeries.map ψ (omegaExpansionWeierstrass h₀ hf hdeg hω hωu)
      = ∑ i, cs i • omegaPrime ΦK ζK i := by
  have hXne : (PowerSeries.X : K⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  refine mul_left_cancel₀ hXne ?_
  calc PowerSeries.X * PowerSeries.map ψ (omegaExpansionWeierstrass h₀ hf hdeg hω hωu)
      = PowerSeries.map ψ (PowerSeries.X * omegaExpansionWeierstrass h₀ hf hdeg hω hωu) := by
        rw [map_mul, PowerSeries.map_X]
    _ = aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) (h₀.map ψ)
        * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu)) := by
        rw [X_mul_omegaExpansionWeierstrass, map_mul, PowerSeries.map_aeval,
          PowerSeries.map_derivative]
    _ = ∑ i, cs i • (aeval (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))
          (tracePoly (uτ.map ψ) (c₂.map ψ) i)
        * PowerSeries.derivative (PowerSeries.map ψ (weierstrassSeries hf hdeg hω hωu))) := by
        rw [hmap, map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_mul_assoc]
    _ = ∑ i, cs i • (PowerSeries.X * omegaPrime ΦK ζK i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [X_mul_omegaPrime_eq_aeval_mul_derivative dg hf hdeg hω hωu hsep hm hm₀ hyQ huτ
          hdvdτ hgτ hcerts hcertsg ΦK ζK hζK N hN i (hPglob i)]
    _ = PowerSeries.X * ∑ i, cs i • omegaPrime ΦK ζK i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ (mul_smul_comm _ _ _).symm

end WeierstrassCapstone

end ChabautyColeman

end
