/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.GlobalDiff
public import HyperellipticCurves.Log.Trace.TraceDisk

/-!
# The disk-expansion trace-matrix transport, over the function field

The function-field counterpart of `HyperellipticCurves.Log.Trace.TraceDisk`:
`ChabautyColeman.globExpand_traceMat`, the transport of the global trace matrix to the disk
one along the disk expansion. The main theorems do not depend on this file: the counting route
identifies the expansions per disk over `Frac(K⟦z⟧)`, without the function field.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section GlobTrace

open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K] [CharZero K]
  [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]
  {sφ cφ : Polynomial O⟦X⟧}
  {sP cP : Polynomial (HypField K (f.map ψ))} {i j : ℕ}

/-- **The global trace matrix expands to the disk one.** Applying the disk expansion to the
trace matrix of the global chart datum gives the trace matrix of the per-disk datum: the
expansion is a ring homomorphism, so it passes through the matrix
(`ChabautyColeman.traceMat_map`), and it carries the global pipeline to the `φ`-pipeline
(`ChabautyColeman.map_globExpand_globPipeline`). -/
theorem globExpand_traceMat
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
    (hsφ : cφ * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1
      + sφ * (2 * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2) = 1)
    (hsP : cP * (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg).1
      + sP * (2 * (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)
        dg).2) = 1) :
    globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
        (traceMat (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)
          dg).1 sP i j)
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ))
          (traceMat (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1 sφ i j) := by
  obtain ⟨hφm, -, -⟩ :=
    phiPipeline_monic_dvd_degree_lt hsep hm hm₀ hb hfa h2 hyQ huτ hdvdτ hcerts
  have hsepK : ψ a ≠ ψ xQ := by
    intro hc
    have hun : IsUnit (ψ xQ - ψ a) := by rw [← map_sub]; exact IsUnit.map ψ hsep
    rw [hc, sub_self] at hun
    exact not_isUnit_zero hun
  have hm₀K : ψ m₀ * (ψ a - ψ xQ) = -ψ b - ψ yQ := map_slope ψ hm₀
  have hyQK : (ψ yQ) ^ 2 = (f.map ψ).eval (ψ xQ) := by
    rw [eval_map, Polynomial.eval₂_at_apply, ← map_pow, hyQ]
  obtain ⟨hgm, -, -⟩ := globPipeline_monic_dvd_degree_lt (f.map ψ) (uτ.map ψ) (vτ.map ψ)
    (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg (b := ψ b) hsepK hm₀K hbK hyQK (huτ.map ψ)
    (map_dvd_sq_sub ψ hdvdτ) (by rwa [huτ.natDegree_map])
  obtain ⟨h1, h2'⟩ := Prod.ext_iff.mp (map_globExpand_globPipeline dg hbK hfaK hf hsep hm hm₀
    hb hfa h2 hyQ huτ hdvdτ hgτ hcerts hcertsg)
  dsimp only at h1 h2'
  set E := globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
  set ρ := (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)
  have hEb : cP.map E * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map ρ
      + sP.map E * (2 * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2.map ρ) = 1 := by
    have h := map_bezout E hsP
    rwa [h1, h2'] at h
  have hρb : cφ.map ρ * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map ρ
      + sφ.map ρ * (2 * (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2.map ρ) = 1 := by
    exact map_bezout ρ hsφ
  rw [← traceMat_map E hgm sP i j, ← traceMat_map ρ hφm sφ i j, h1]
  exact traceMat_congr (hφm.map ρ) hEb hρb i j

end GlobTrace

end ChabautyColeman

end
