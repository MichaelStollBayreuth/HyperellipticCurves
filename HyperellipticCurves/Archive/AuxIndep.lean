/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Log.Charts.PhiChart

/-!
# Auxiliary-point independence of the disk pipeline

Clause (a) of `thm:omega-prime-global`: two runs of the `def:phiD` pipeline through different
auxiliary points produce the same Mumford datum over `O⟦z⟧`. The main theorems do not depend on
it: the trace-form route identifies every disk expansion with the same global `tracePoly`
combination, so the auxiliary point cannot affect anything the count sees.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section AuxIndep

open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] {f : O[X]} {a b xQ yQ xQ' yQ' : O}
  {m m' : O⟦X⟧} {m₀ m₀' : O} {uτ vτ : O[X]} {d d' : CantorCertData O⟦X⟧}
  [CharZero (FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The disk pipeline is independent of the auxiliary point** (blueprint
`thm:omega-prime-global`(a)): two runs of the `def:phiD` pipeline through different
auxiliary points `Q`, `Q'` (with their own slope certificates and certificate packs)
produce the same Mumford datum over `O⟦z⟧` — the auxiliary classes cancel, so over
`Frac(O⟦z⟧)` both outputs are reduced representatives of the same class. In particular
the chart coordinates `ζ(z)` and the differential `ω′` do not depend on `Q`. -/
theorem phiPipeline_eq_of_aux (hf : f.Monic)
    (hsep : IsUnit (xQ - a)) (hsep' : IsUnit (xQ' - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm' : m' * (PowerSeries.C xQ' - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ') - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hm₀' : m₀' * (a - xQ') = -b - yQ')
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ) (hyQ' : yQ' ^ 2 = f.eval xQ')
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hcerts' : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ' yQ' m' m₀' uτ vτ) d'
      uτ.natDegree) :
    phiPipeline f a b xQ yQ m m₀ uτ vτ d = phiPipeline f a b xQ' yQ' m' m₀' uτ vτ d' := by
  classical
  set Kz := FractionRing (PowerSeries O) with hKzdef
  set ρ : O⟦X⟧ →+* Kz := algebraMap (PowerSeries O) Kz with hρdef
  have hinj : Function.Injective ρ := IsFractionRing.injective (PowerSeries O) Kz
  have hCinj : Function.Injective (PowerSeries.C : O →+* O⟦X⟧) :=
    Function.LeftInverse.injective fun x ↦ PowerSeries.constantCoeff_C x
  have hφzinj : Function.Injective (ρ.comp (PowerSeries.C : O →+* O⟦X⟧)) :=
    hinj.comp hCinj
  -- characteristic-zero and squarefree facts over `Kz`
  have hchO : CharZero O := (algebraMap O (FractionRing O)).charZero
  have hchz : CharZero O⟦X⟧ := (PowerSeries.constantCoeff : O⟦X⟧ →+* O).charZero
  have hchKz : CharZero Kz := charZero_of_injective_algebraMap hinj
  have h2Kz : NeZero (2 : Kz) := ⟨by norm_num⟩
  set F : (O⟦X⟧)[X] := f.map PowerSeries.C with hFdef
  have hFρ : F.map ρ = f.map (ρ.comp (PowerSeries.C : O →+* O⟦X⟧)) := by
    rw [hFdef, Polynomial.map_map]
  have hOddKz : Fact (Odd ((F.map ρ)).natDegree) := ⟨by
    rw [hFρ, hf.natDegree_map]
    have h := (Fact.out : Odd ((f.map (algebraMap O (FractionRing O))).natDegree))
    rwa [hf.natDegree_map] at h⟩
  have hSqKz : Fact (Squarefree (F.map ρ)) := ⟨by
    rw [hFρ]
    have hψeq : f.map (ρ.comp (PowerSeries.C : O →+* O⟦X⟧))
        = (f.map (algebraMap O (FractionRing O))).map (IsFractionRing.lift hφzinj) := by
      rw [Polynomial.map_map]
      congr 1
      ext x
      simp only [RingHom.comp_apply]
      rw [IsFractionRing.lift_algebraMap]
      rfl
    rw [hψeq]
    exact ((PerfectField.separable_iff_squarefree.mpr Fact.out).map).squarefree⟩
  -- the pipeline data over `O⟦z⟧`, both runs
  have hu₁ : (phiU₁ a xQ (O := O)).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₁' : (phiU₁ a xQ' (O := O)).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hu₃ : (phiU₃ a xQ (O := O)).Monic :=
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hu₃' : (phiU₃ a xQ' (O := O)).Monic :=
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₁ : phiU₁ a xQ ∣ phiV₁ f a b m ^ 2 - F := movingPair_dvd hsep hm hb hfa h2 hyQ
  have hd₁' : phiU₁ a xQ' ∣ phiV₁ f a b m' ^ 2 - F :=
    movingPair_dvd hsep' hm' hb hfa h2 hyQ'
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧) ∣ (vτ.map PowerSeries.C) ^ 2 - F :=
    map_dvd_sq_sub _ hdvdτ
  have hsepn : IsUnit (a - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hsepn' : IsUnit (a - xQ') := by rw [← neg_sub]; exact hsep'.neg
  have hd₃ : phiU₃ a xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - F :=
    map_dvd_sq_sub _ (pair_dvd hsepn hm₀ hyQ (by rwa [neg_pow_two]))
  have hd₃' : phiU₃ a xQ' ∣ phiV₃ xQ' yQ' m₀' ^ 2 - F :=
    map_dvd_sq_sub _ (pair_dvd hsepn' hm₀' hyQ' (by rwa [neg_pow_two]))
  -- transported certificate packs and mapped-pipeline identities
  have hcertsKz := hcerts.map ρ hu₁ hu₂ hu₃
  have hcertsKz' := hcerts'.map ρ hu₁' hu₂ hu₃'
  have hmap := map_cantorPipeline_generic ρ hu₁ hu₂ hu₃ hcerts
  have hmap' := map_cantorPipeline_generic ρ hu₁' hu₂ hu₃' hcerts'
  -- identification of the mapped pair data
  have hidu₁ : (phiU₁ a xQ).map ρ
      = (X - C (ρ (PowerSeries.C a + PowerSeries.X))) * (X - C (ρ (PowerSeries.C xQ))) := by
    simp only [phiU₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C]
  have hidu₁' : (phiU₁ a xQ').map ρ
      = (X - C (ρ (PowerSeries.C a + PowerSeries.X))) * (X - C (ρ (PowerSeries.C xQ'))) := by
    simp only [phiU₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C]
  have hidv₁ : (phiV₁ f a b m).map ρ = pairV (ρ (PowerSeries.C a + PowerSeries.X))
      (ρ (PowerSeries.C b * diskSeriesGeneric f a)) (ρ m) := by
    rw [phiV₁, pairV_map]
  have hidv₁' : (phiV₁ f a b m').map ρ = pairV (ρ (PowerSeries.C a + PowerSeries.X))
      (ρ (PowerSeries.C b * diskSeriesGeneric f a)) (ρ m') := by
    rw [phiV₁, pairV_map]
  have hidu₃ : (phiU₃ a xQ).map ρ
      = (X - C (ρ (PowerSeries.C xQ))) * (X - C (ρ (PowerSeries.C a))) := by
    rw [phiU₃, Polynomial.map_map]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C, RingHom.comp_apply]
  have hidu₃' : (phiU₃ a xQ').map ρ
      = (X - C (ρ (PowerSeries.C xQ'))) * (X - C (ρ (PowerSeries.C a))) := by
    rw [phiU₃, Polynomial.map_map]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C, RingHom.comp_apply]
  have hidv₃ : (phiV₃ xQ yQ m₀).map ρ = pairV (ρ (PowerSeries.C xQ))
      (ρ (PowerSeries.C yQ)) (ρ (PowerSeries.C m₀)) := by
    rw [phiV₃, Polynomial.map_map, pairV_map]
    simp only [RingHom.comp_apply]
  have hidv₃' : (phiV₃ xQ' yQ' m₀').map ρ = pairV (ρ (PowerSeries.C xQ'))
      (ρ (PowerSeries.C yQ')) (ρ (PowerSeries.C m₀')) := by
    rw [phiV₃, Polynomial.map_map, pairV_map]
    simp only [RingHom.comp_apply]
  -- the point conditions over `Kz`
  have hevalρ (p : (O⟦X⟧)[X]) (w : O⟦X⟧) : (p.map ρ).eval (ρ w) = ρ (p.eval w) := by
    rw [eval_map, eval₂_at_apply]
  have hCeval (x y : O) (hxy : y ^ 2 = f.eval x) :
      ρ (PowerSeries.C y) ^ 2 = (F.map ρ).eval (ρ (PowerSeries.C x)) := by
    rw [hevalρ, ← map_pow, ← map_pow, hxy, hFdef, eval_map, eval₂_at_apply]
  have hPz : ρ (PowerSeries.C b * diskSeriesGeneric f a) ^ 2
      = (F.map ρ).eval (ρ (PowerSeries.C a + PowerSeries.X)) := by
    rw [hevalρ, ← map_pow, diskY_sq hb hfa h2, hFdef]
  have hnePz (x : O) (hx : IsUnit (x - a)) :
      ρ (PowerSeries.C a + PowerSeries.X) ≠ ρ (PowerSeries.C x) := by
    intro h
    have hunit : IsUnit (ρ (PowerSeries.C x - (PowerSeries.C a + PowerSeries.X))) :=
      (isUnit_C_sub_diskX hx).map ρ
    rw [map_sub, ← h, sub_self] at hunit
    exact not_isUnit_zero hunit
  have hneQa (x : O) (hx : IsUnit (x - a)) :
      ρ (PowerSeries.C x) ≠ ρ (PowerSeries.C a) := fun h ↦ by
    have := hφzinj (a₁ := x) (a₂ := a) (by simpa [RingHom.comp_apply] using h)
    exact hx.ne_zero (by rw [this, sub_self])
  have hmPQ : ρ m * (ρ (PowerSeries.C xQ) - ρ (PowerSeries.C a + PowerSeries.X))
      = -ρ (PowerSeries.C yQ) - ρ (PowerSeries.C b * diskSeriesGeneric f a) := by
    have h := congrArg ρ hm
    rw [map_mul, map_sub, map_sub,
      show ρ (PowerSeries.C (-yQ)) = -ρ (PowerSeries.C yQ) from by rw [map_neg, map_neg]]
      at h
    exact h
  have hmPQ' : ρ m' * (ρ (PowerSeries.C xQ') - ρ (PowerSeries.C a + PowerSeries.X))
      = -ρ (PowerSeries.C yQ') - ρ (PowerSeries.C b * diskSeriesGeneric f a) := by
    have h := congrArg ρ hm'
    rw [map_mul, map_sub, map_sub,
      show ρ (PowerSeries.C (-yQ')) = -ρ (PowerSeries.C yQ') from by rw [map_neg, map_neg]]
      at h
    exact h
  have hCmap (x : O) : ρ (PowerSeries.C x) = (ρ.comp (PowerSeries.C : O →+* O⟦X⟧)) x :=
    rfl
  have hmQR : ρ (PowerSeries.C m₀)
      * (ρ (PowerSeries.C a) - ρ (PowerSeries.C xQ))
      = -ρ (PowerSeries.C b) - ρ (PowerSeries.C yQ) := by
    have h := congrArg (ρ.comp (PowerSeries.C : O →+* O⟦X⟧)) hm₀
    simpa only [map_mul, map_sub, map_neg, hCmap] using h
  have hmQR' : ρ (PowerSeries.C m₀')
      * (ρ (PowerSeries.C a) - ρ (PowerSeries.C xQ'))
      = -ρ (PowerSeries.C b) - ρ (PowerSeries.C yQ') := by
    have h := congrArg (ρ.comp (PowerSeries.C : O →+* O⟦X⟧)) hm₀'
    simpa only [map_mul, map_sub, map_neg, hCmap] using h
  -- the class identity: the auxiliary parts cancel
  have hpair := mk0_pair_mul_mk0_pair_chain (f := F.map ρ) (hnePz xQ hsep)
    (hneQa xQ hsep) hmPQ hmQR hPz (hCeval xQ yQ hyQ) (hCeval a b hb)
  have hpair' := mk0_pair_mul_mk0_pair_chain (f := F.map ρ) (hnePz xQ' hsep')
    (hneQa xQ' hsep') hmPQ' hmQR' hPz (hCeval xQ' yQ' hyQ') (hCeval a b hb)
  -- rewrite everything to the concrete pair data over `Kz`
  have hidD : (phiConfig f a b xQ yQ m m₀ uτ vτ).map ρ
      = ⟨(X - C (ρ (PowerSeries.C a + PowerSeries.X))) * (X - C (ρ (PowerSeries.C xQ))),
        pairV (ρ (PowerSeries.C a + PowerSeries.X))
          (ρ (PowerSeries.C b * diskSeriesGeneric f a)) (ρ m),
        (uτ.map PowerSeries.C).map ρ, (vτ.map PowerSeries.C).map ρ,
        (X - C (ρ (PowerSeries.C xQ))) * (X - C (ρ (PowerSeries.C a))),
        pairV (ρ (PowerSeries.C xQ)) (ρ (PowerSeries.C yQ)) (ρ (PowerSeries.C m₀))⟩ := by
    simp only [PipelineData.map, phiConfig, diskConfig, hidu₁, hidv₁, hidu₃, hidv₃]
  have hidD' : (phiConfig f a b xQ' yQ' m' m₀' uτ vτ).map ρ
      = ⟨(X - C (ρ (PowerSeries.C a + PowerSeries.X))) * (X - C (ρ (PowerSeries.C xQ'))),
        pairV (ρ (PowerSeries.C a + PowerSeries.X))
          (ρ (PowerSeries.C b * diskSeriesGeneric f a)) (ρ m'),
        (uτ.map PowerSeries.C).map ρ, (vτ.map PowerSeries.C).map ρ,
        (X - C (ρ (PowerSeries.C xQ'))) * (X - C (ρ (PowerSeries.C a))),
        pairV (ρ (PowerSeries.C xQ')) (ρ (PowerSeries.C yQ')) (ρ (PowerSeries.C m₀'))⟩ := by
    simp only [PipelineData.map, phiConfig, diskConfig, hidu₁', hidv₁', hidu₃', hidv₃']
  rw [hidD] at hcertsKz hmap
  rw [hidD'] at hcertsKz' hmap'
  have hu₁K : ((X - C (ρ (PowerSeries.C a + PowerSeries.X)))
      * (X - C (ρ (PowerSeries.C xQ)))).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₁K' : ((X - C (ρ (PowerSeries.C a + PowerSeries.X)))
      * (X - C (ρ (PowerSeries.C xQ')))).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂K : ((uτ.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ).Monic := hu₂.map ρ
  have hu₃K : ((X - C (ρ (PowerSeries.C xQ)))
      * (X - C (ρ (PowerSeries.C a)))).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₃K' : ((X - C (ρ (PowerSeries.C xQ')))
      * (X - C (ρ (PowerSeries.C a)))).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hd₁K := map_dvd_sq_sub ρ hd₁
  rw [hidu₁, hidv₁] at hd₁K
  have hd₁K' := map_dvd_sq_sub ρ hd₁'
  rw [hidu₁', hidv₁'] at hd₁K'
  have hd₂K := map_dvd_sq_sub ρ hd₂
  have hd₃K := map_dvd_sq_sub ρ hd₃
  rw [hidu₃, hidv₃] at hd₃K
  have hd₃K' := map_dvd_sq_sub ρ hd₃'
  rw [hidu₃', hidv₃'] at hd₃K'
  have hgK : 2 * uτ.natDegree < (F.map ρ).natDegree := by
    rw [hFρ, hf.natDegree_map]
    exact hgτ
  -- both pipelines over `Kz` have the same input class product, hence the same output
  have heq := cantorPipeline_eq_cantorPipeline_of_mk0_eq hu₁K hd₁K hu₂K hd₂K hu₃K hd₃K
    hu₁K' hd₁K' hu₂K hd₂K hu₃K' hd₃K' hcertsKz hcertsKz' hgK
    (by rw [mul_right_comm, hpair, ← hpair', mul_right_comm])
  -- combine and descend along the injective `ρ`
  have hcomb := hmap.trans (heq.trans hmap'.symm)
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hcomb
  dsimp only at h1 h2
  exact Prod.ext (Polynomial.map_injective ρ hinj h1) (Polynomial.map_injective ρ hinj h2)

end AuxIndep


end ChabautyColeman

end
