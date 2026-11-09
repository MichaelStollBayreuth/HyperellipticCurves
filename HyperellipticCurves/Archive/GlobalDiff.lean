/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.DiskExpand
public import HyperellipticCurves.Log.Charts.DiskIdentification
public import HyperellipticCurves.Log.Ftau.DeltaRational

import HyperellipticCurves.Log.Trace.TraceDisk

/-!
# The canonical global inverse differential matrix (`thm:omega-prime-global`)

This file realizes the matrix `N` of the global differential numerators
`ChabautyColeman.globOmega` — the inverse differential matrix `M⁻¹` of the translated
formal group law evaluated along the chart coordinates — as an actual matrix over the
function field, and proves its defining property `hN` (the hypothesis of
`ChabautyColeman.globExpand_globOmega`).

The mechanism: by `ChabautyColeman.invariantDiffFold_rational` the entries of `M` are
specializations of universal elements `M′` of the localized three-block family ring
(`ChabautyColeman.DatumFamRing`).  The same family ring also specializes along the
**global** three-block Mumford datum (`ChabautyColeman.globFamU`/`globFamV`/`globFamW`:
the global pipeline output plus twice the `τ`-center), and the two specializations are
intertwined by the disk expansion `ChabautyColeman.globExpand`
(`ChabautyColeman.globExpand_comp_datumFamSpec`) — because coefficientwise the global
blocks expand to the `Y = 0`, chart-coordinate substitution of the per-disk chart data
(`ChabautyColeman.map_chartU_eq_phiPipeline_fst`,
`ChabautyColeman.map_chartV_eq_phiPipeline_snd`; the latter is square-root uniqueness
over the local ring `O⟦z⟧`).  The unit-denominator condition transfers for free
(`ChabautyColeman.isUnit_datumFamSpec_of_isUnit_ftauFamSpec`), so `M′` specializes to a
matrix over the function field whose expansion is `M(ζ(z))`; inverting over the function
field and using uniqueness of inverses gives `N` with `hN`, together with the direct
matrix `NdM` (its own expansion identity and `NdM * N = 1`), so that infinity-integrality
of `N` follows from that of `NdM` via
`ChabautyColeman.inftyOrd_matrix_inv_nonneg_of_mul_eq_one`
(`ChabautyColeman.exists_globN`).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section GlobalFam

open HypField

variable {K : Type*} [Field K] (f : K[X]) [Fact (Odd f.natDegree)]

/-- The `u`-polynomials of the global three-block family datum: the global pipeline
output and (twice) the `τ`-center. -/
noncomputable def globFamU (uτ vτ : K[X]) (a xQ yQ m₀ : K)
    (d : CantorCertData (HypField K f)) : Fin 3 → (HypField K f)[X] :=
  ![(globPipeline f uτ vτ a xQ yQ m₀ d).1,
    uτ.map (algebraMap K (HypField K f)), uτ.map (algebraMap K (HypField K f))]

/-- The `v`-polynomials of the global three-block family datum. -/
noncomputable def globFamV (uτ vτ : K[X]) (a xQ yQ m₀ : K)
    (d : CantorCertData (HypField K f)) : Fin 3 → (HypField K f)[X] :=
  ![(globPipeline f uτ vτ a xQ yQ m₀ d).2,
    vτ.map (algebraMap K (HypField K f)), vτ.map (algebraMap K (HypField K f))]

/-- The cofactor polynomials of the global three-block family datum. -/
noncomputable def globFamW (uτ vτ : K[X]) (a xQ yQ m₀ : K)
    (d : CantorCertData (HypField K f)) (w : K[X]) : Fin 3 → (HypField K f)[X] :=
  ![cantorCofactor (f.map (algebraMap K (HypField K f)))
      (globPipeline f uτ vτ a xQ yQ m₀ d).1 (globPipeline f uτ vτ a xQ yQ m₀ d).2,
    w.map (algebraMap K (HypField K f)), w.map (algebraMap K (HypField K f))]

end GlobalFam

section SideConditions

variable {K : Type*} [Field K] {f uτ vτ w : K[X]} {a b xQ yQ m₀ : K}
  {d : CantorCertData (HypField K f)} {n : ℕ} [Fact (Odd f.natDegree)]

variable (hsep' : a ≠ xQ) (hm₀ : m₀ * (a - xQ) = -b - yQ) (hb : b ^ 2 = f.eval a)
  (hyQ : yQ ^ 2 = f.eval xQ) (huτ : uτ.Monic) (hvτ : vτ.degree < uτ.degree)
  (hwτ : vτ ^ 2 - f = uτ * w)
  (hcerts : IsPipelineCerts (f.map (algebraMap K (HypField K f))) (globConfig f uτ vτ a xQ yQ m₀) d
    uτ.natDegree)

include hsep' hm₀ hb hyQ huτ hwτ hcerts in
/-- The global three-block datum blocks are monic. -/
theorem globFamU_monic (i : Fin 3) : (globFamU f uτ vτ a xQ yQ m₀ d i).Monic := by
  fin_cases i
  · exact (globPipeline_monic_dvd_degree_lt f uτ vτ a xQ yQ m₀ d hsep' hm₀ hb hyQ huτ
      ⟨w, hwτ⟩ hcerts).1
  · exact huτ.map _
  · exact huτ.map _

include huτ hcerts in
/-- The global three-block datum blocks have `natDegree` `n`. -/
theorem globFamU_natDegree (hne : uτ.natDegree = n) (i : Fin 3) :
    (globFamU f uτ vτ a xQ yQ m₀ d i).natDegree = n := by
  fin_cases i
  · exact hcerts.hdeg.trans hne
  · exact (huτ.natDegree_map _).trans hne
  · exact (huτ.natDegree_map _).trans hne

include hsep' hm₀ hb hyQ huτ hvτ hwτ hcerts in
/-- The global three-block `v`-parts have degree `< n`. -/
theorem globFamV_degree (hne : uτ.natDegree = n) (i : Fin 3) :
    (globFamV f uτ vτ a xQ yQ m₀ d i).degree < (n : WithBot ℕ) := by
  have hdegu : uτ.degree = (n : WithBot ℕ) := by
    rw [degree_eq_natDegree huτ.ne_zero, hne]
  fin_cases i
  · have h := (globPipeline_monic_dvd_degree_lt f uτ vτ a xQ yQ m₀ d hsep' hm₀ hb hyQ huτ
      ⟨w, hwτ⟩ hcerts)
    refine h.2.2.trans_eq ?_
    rw [degree_eq_natDegree h.1.ne_zero, globPipeline, hcerts.hdeg, hne]
  · exact Polynomial.degree_map_le.trans_lt (hvτ.trans_eq hdegu)
  · exact Polynomial.degree_map_le.trans_lt (hvτ.trans_eq hdegu)

include hsep' hm₀ hb hyQ huτ hwτ hcerts in
/-- The global three-block data satisfy the curve relation. -/
theorem globFamW_sq_sub (i : Fin 3) :
    globFamV f uτ vτ a xQ yQ m₀ d i ^ 2 - f.map (algebraMap K (HypField K f))
      = globFamU f uτ vτ a xQ yQ m₀ d i * globFamW f uτ vτ a xQ yQ m₀ d w i := by
  have hmap : (vτ.map (algebraMap K (HypField K f))) ^ 2
        - f.map (algebraMap K (HypField K f))
      = uτ.map (algebraMap K (HypField K f)) * w.map (algebraMap K (HypField K f)) := by
    have h := congrArg (Polynomial.map (algebraMap K (HypField K f))) hwτ
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul] using h
  fin_cases i
  · exact cantorCofactor_spec _
      (globPipeline_monic_dvd_degree_lt f uτ vτ a xQ yQ m₀ d hsep' hm₀ hb hyQ huτ ⟨w, hwτ⟩ hcerts).1
      (globPipeline_monic_dvd_degree_lt f uτ vτ a xQ yQ m₀ d hsep' hm₀ hb hyQ huτ
        ⟨w, hwτ⟩ hcerts).2.1
  · exact hmap
  · exact hmap

include hsep' hm₀ hb hyQ huτ hvτ hwτ hcerts in
/-- The global three-block cofactors satisfy the family degree bound. -/
theorem globFamW_degree (hne : uτ.natDegree = n) (i : Fin 3) :
    (globFamW f uτ vτ a xQ yQ m₀ d w i).degree
      < ((ftauKBound (f.map (algebraMap K (HypField K f))) n : WithBot ℕ) + 1) := by
  have hV := globFamV_degree hsep' hm₀ hb hyQ huτ hvτ hwτ hcerts hne
  have hU := globFamU_monic hsep' hm₀ hb hyQ huτ hwτ hcerts
  have hUn := globFamU_natDegree huτ hcerts hne
  have hrel := globFamW_sq_sub hsep' hm₀ hb hyQ huτ hwτ hcerts (w := w)
  refine degree_lt_add_one_of_natDegree_le ?_
  have h := natDegree_cofactor_le_of_sq_sub (hU i) (by rw [hUn i]; exact hV i) (hrel i)
  rw [hUn i] at h
  exact h

end SideConditions

section GlobalSpec

open HypField
open scoped PowerSeries

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [NeZero (2 : K)] {ψ : O →+* K}
  {n : ℕ} {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧} {dg : CantorCertData (HypField K (f.map ψ))}

/-- The disk expansion of the `ψ`-image of a base constant is the constant power
series, as a homomorphism identity. -/
theorem globExpand_comp_algebraMap_comp_eq {hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)}
    {hfaK : (f.map ψ).eval (ψ a) ≠ 0} :
    (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK).comp
        ((algebraMap K (HypField K (f.map ψ))).comp ψ)
      = ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp (PowerSeries.C : O →+* O⟦X⟧) := by
  refine RingHom.ext fun c ↦ ?_
  simp only [RingHom.comp_apply]
  rw [globExpand_algebraMap_base, PowerSeries.map_C]

variable (θ : MvPowerSeries (Fin n) O →+* O⟦X⟧)

/-- The coefficient homomorphism composite `ρ' ∘ θ ∘ setYZero` restricts to constants
compatibly with the disk expansion of the function-field constants. -/
theorem comp_setYZero_comp_C_eq
    (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)
    {hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)} {hfaK : (f.map ψ).eval (ψ a) ≠ 0} :
    ((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ).comp setYZero).comp
        (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK).comp
          ((algebraMap K (HypField K (f.map ψ))).comp ψ) := by
  refine RingHom.ext fun c ↦ ?_
  simp only [RingHom.comp_apply]
  rw [show setYZero (MvPowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries (Fin n) O)
      from RingHom.congr_fun setYZero_comp_C c,
    show θ (MvPowerSeries.C c) = PowerSeries.C c from RingHom.congr_fun hθC c,
    PowerSeries.map_C, globExpand_algebraMap_base]

variable (hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = PowerSeries.C)

include hθC in
/-- Transport of a constant (`τ`-datum) polynomial block: the `Y = 0` / chart-coordinate
composite on the `MvPowerSeries.C`-image equals the disk expansion of the function-field
image. -/
theorem map_map_C_comp (p : O[X]) (hbK' : (ψ b) ^ 2 = (f.map ψ).eval (ψ a))
    (hfaK' : (f.map ψ).eval (ψ a) ≠ 0) :
    ((p.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map
        ((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ).comp setYZero))
      = ((p.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map
          (globExpand (f.map ψ) (ψ a) (ψ b) hbK' hfaK') := by
  simp only [Polynomial.map_map]
  exact congrArg (Polynomial.map · p) (comp_setYZero_comp_C_eq θ hθC)

include hθC in
/-- Variant of `ChabautyColeman.map_map_C_comp` for constants already at `Y = 0`. -/
theorem map_map_C_fin_comp (p : O[X]) (hbK' : (ψ b) ^ 2 = (f.map ψ).eval (ψ a))
    (hfaK' : (f.map ψ).eval (ψ a) ≠ 0) :
    ((p.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)).map
        ((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ)))
      = ((p.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map
          (globExpand (f.map ψ) (ψ a) (ψ b) hbK' hfaK') := by
  simp only [Polynomial.map_map]
  refine congrArg (Polynomial.map · p) (RingHom.ext fun c ↦ ?_)
  simp only [RingHom.comp_apply]
  rw [show θ (MvPowerSeries.C c) = PowerSeries.C c from RingHom.congr_fun hθC c,
    PowerSeries.map_C, globExpand_algebraMap_base]

variable [Fact (Odd (f.map ψ).natDegree)]

variable
  (hθX : ∀ j : Fin n, ∀ hne : uτ.natDegree = n,
    θ (MvPowerSeries.X j) = phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))
  {hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)} {hfaK : (f.map ψ).eval (ψ a) ≠ 0}
  (hf : f.Monic) (hsep : IsUnit (xQ - a))
  (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
    = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
  (hm₀ : m₀ * (a - xQ) = -b - yQ)
  (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
  (hyQ : yQ ^ 2 = f.eval xQ)
  (hu : uτ.Monic) (hne : uτ.natDegree = n) (hv : vτ.degree < uτ.degree)
  (hw : vτ ^ 2 - f = uτ * w) (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
  (hgτ : 2 * uτ.natDegree < f.natDegree)
  (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d uτ.natDegree)
  (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
    (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
    uτ.natDegree)

variable [IsDomain O] [CharZero K] [Fact (Squarefree (f.map ψ))]

include hθC hθX hf hsep hm hm₀ hb hfa h2 hyQ hu hne hgτ hcerts hcertsg in
/-- **Block transport, `u`-parts**: the chart-coordinate composite takes the three-block
`u`-data of the `F_τ` specialization to the disk expansions of the global three-block
`u`-data. -/
theorem map_ftauFamU_globExpand (hdvdτ : uτ ∣ vτ ^ 2 - f) (b' : Fin 3) :
    (ftauFamU uτ n b').map
        ((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ).comp setYZero)
      = (globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg b').map
          (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK) := by
  have hpipe := map_globExpand_globPipeline dg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ hu
    hdvdτ hgτ hcerts hcertsg
  injection hpipe with hp1 hp2
  obtain ⟨hPmonic, -, -⟩ := phiPipeline_monic_dvd_degree_lt hsep hm hm₀ hb hfa h2 hyQ hu
    hdvdτ hcerts
  fin_cases b'
  · change (ftauUX uτ n).map _ = (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ)
      (ψ yQ) (ψ m₀) dg).1.map _
    rw [← Polynomial.map_map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* _),
      ftauUX_map_setYZero, ← Polynomial.map_map θ, map_chartU_eq_phiPipeline_fst hne θ hθC
      (fun j ↦ hθX j hne) hu hPmonic hcerts.hdeg, ← hp1]
  · change (ftauUY uτ n).map _ = ((uτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map _
    rw [← Polynomial.map_map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* _),
      ftauUY_map_setYZero, map_map_C_fin_comp θ hθC uτ hbK hfaK]
  · exact map_map_C_comp θ hθC uτ hbK hfaK

variable [IsLocalRing O] [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  (hθ0 : ∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g)

include hθC hθX hθ0 hf hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw hbez hgτ hcerts hcertsg in
/-- **Block transport, `v`-parts**. -/
theorem map_ftauFamV_globExpand (b' : Fin 3) :
    (ftauFamV hu hne hv hw hbez b').map
        ((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ).comp setYZero)
      = (globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg b').map
          (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK) := by
  have hpipe := map_globExpand_globPipeline dg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ hu
    ⟨w, hw⟩ hgτ hcerts hcertsg
  injection hpipe with hp1 hp2
  fin_cases b'
  · change (ftauVX hu hne hv hw hbez).map _ = (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ)
      (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg).2.map _
    rw [← Polynomial.map_map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* _),
      ftauVX_map_setYZero, ← Polynomial.map_map θ, map_chartV_eq_phiPipeline_snd hne θ hθC
      (fun j ↦ hθX j hne) hθ0 hf hsep hm hm₀ hb hfa h2 hyQ hu hv hw hbez hgτ hcerts, ← hp2]
  · change (ftauVY hu hne hv hw hbez).map _
      = ((vτ.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map _
    rw [← Polynomial.map_map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* _),
      ftauVY_map_setYZero, map_map_C_fin_comp θ hθC vτ hbK hfaK]
  · exact map_map_C_comp θ hθC vτ hbK hfaK

include hθC hθX hθ0 hf hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw hbez hgτ hcerts hcertsg in
/-- **Block transport, cofactors**. -/
theorem map_ftauFamW_globExpand (b' : Fin 3) :
    (ftauFamW hu hne hv hw hbez b').map
        ((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ).comp setYZero)
      = (globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
          (w.map ψ) b').map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK) := by
  have hpipe := map_globExpand_globPipeline dg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ hu
    ⟨w, hw⟩ hgτ hcerts hcertsg
  injection hpipe with hp1 hp2
  obtain ⟨hPmonic, -, -⟩ := phiPipeline_monic_dvd_degree_lt hsep hm hm₀ hb hfa h2 hyQ hu
    ⟨w, hw⟩ hcerts
  -- K-side facts for the monicity of the global pipeline
  have hyQK : (ψ yQ) ^ 2 = (f.map ψ).eval (ψ xQ) := map_sq_eq_eval_map ψ hyQ
  have hsepK : ψ a ≠ ψ xQ := map_ne_of_isUnit_sub ψ hsep
  have hm₀K : (ψ m₀) * (ψ a - ψ xQ) = -(ψ b) - ψ yQ := map_slope ψ hm₀
  have hcertsg' : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      (uτ.map ψ).natDegree := by
    rwa [hu.natDegree_map ψ]
  have hgmonic : (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)
      dg).1.Monic := by
    have hdvdτK : uτ.map ψ ∣ (vτ.map ψ) ^ 2 - f.map ψ := ⟨w.map ψ, by
      have h := congrArg (Polynomial.map ψ) hw
      simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul] using h⟩
    exact (globPipeline_monic_dvd_degree_lt (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ)
      (ψ yQ) (ψ m₀) dg hsepK hm₀K hbK hyQK (hu.map ψ) hdvdτK hcertsg').1
  -- the mapped curve polynomial agrees on both routes
  have hFeq : ((f.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map
        (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = (f.map (PowerSeries.C : O →+* O⟦X⟧)).map
          ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
            (PowerSeries.map ψ)) := by
    simp only [Polynomial.map_map]
    exact congrArg (Polynomial.map · f) (globExpand_comp_algebraMap_comp_eq
      (hbK := hbK) (hfaK := hfaK))
  fin_cases b'
  · change (cantorCofactor (f.map MvPowerSeries.C) (ftauUX uτ n) (ftauVX hu hne hv hw hbez)).map _
      = (cantorCofactor ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
          (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg).1
          (globPipeline (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg).2).map _
    rw [show ftauUX uτ n = (chartU uτ n).map
        (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom from rfl,
      show ftauVX hu hne hv hw hbez = (chartV hu hne.ge hv hw hbez).map
        (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom from rfl,
      ← Polynomial.map_map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* _),
      map_cantorCofactor _ _ (chartU_map_rename_monic Sum.inl hu hne.ge)]
    simp only [Polynomial.map_map]
    rw [setYZero_comp_rename_inl, setYZero_comp_C, Polynomial.map_id, Polynomial.map_id,
      ← Polynomial.map_map θ
        ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (PowerSeries.map ψ)),
      map_cantorCofactor _ _ (chartU_monic hu hne.ge), Polynomial.map_map, hθC,
      map_chartU_eq_phiPipeline_fst hne θ hθC (fun j ↦ hθX j hne) hu hPmonic hcerts.hdeg,
      map_chartV_eq_phiPipeline_snd hne θ hθC (fun j ↦ hθX j hne) hθ0 hf hsep hm hm₀ hb
        hfa h2 hyQ hu hv hw hbez hgτ hcerts,
      map_cantorCofactor _ _ hPmonic, map_cantorCofactor _ _ hgmonic, hp1, hp2]
    simp only [Polynomial.map_map]
    rw [globExpand_comp_algebraMap_comp_eq]
  · change (cantorCofactor (f.map MvPowerSeries.C) (ftauUY uτ n) (ftauVY hu hne hv hw hbez)).map _
      = ((w.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map _
    rw [show ftauUY uτ n = (chartU uτ n).map
        (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom from rfl,
      show ftauVY hu hne hv hw hbez = (chartV hu hne.ge hv hw hbez).map
        (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom from rfl,
      ← Polynomial.map_map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* _),
      map_cantorCofactor _ _ (chartU_map_rename_monic Sum.inr hu hne.ge)]
    simp only [Polynomial.map_map]
    rw [setYZero_comp_rename_inr, setYZero_comp_C,
      ← Polynomial.map_map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O)
        (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O),
      ← Polynomial.map_map (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) O →+* O)
        (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O),
      chartU_map_constantCoeff, chartV_map_constantCoeff,
      ← map_cantorCofactor (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) f hu,
      cantorCofactor_eq_of_sq_sub hu hw, Polynomial.map_map]
    refine congrArg (Polynomial.map · w) (RingHom.ext fun c ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [show θ (MvPowerSeries.C c) = PowerSeries.C c from RingHom.congr_fun hθC c,
      PowerSeries.map_C, globExpand_algebraMap_base]
  · change (w.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map _
      = ((w.map ψ).map (algebraMap K (HypField K (f.map ψ)))).map _
    exact map_map_C_comp θ hθC w hbK hfaK

variable [Algebra O (HypField K (f.map ψ))]
  (halg : algebraMap O (HypField K (f.map ψ)) = (algebraMap K (HypField K (f.map ψ))).comp ψ)
  (hgu : ∀ i, (globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg i).Monic)
  (hgm : ∀ i, (globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
    i).natDegree = n)
  (hgv : ∀ i, (globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
    i).degree < (n : WithBot ℕ))
  (hgwd : ∀ i, (globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
    (w.map ψ) i).degree < ((ftauKBound f n : WithBot ℕ) + 1))
  (hgrel : ∀ i, globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg i
      ^ 2 - f.map (algebraMap O (HypField K (f.map ψ)))
    = globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg i
      * globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
          (w.map ψ) i)

include hθC hθX hθ0 halg hf hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw hbez hgτ hcerts
  hcertsg in
/-- **The specialization alignment**: the disk expansion of the global three-block
specialization agrees with the chart-coordinate substitution of the `Y = 0` reduction of the
per-disk chart-data specialization. -/
theorem globExpand_comp_datumFamSpec :
    (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK).comp
        (datumFamSpec (f := f)
          (u := globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
          (v := globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
          (w := globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg (w.map ψ))
          hgu hgm hgv hgwd hgrel)
      = ((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ).comp setYZero).comp
        (ftauFamSpec hu hne hv hw hbez) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun p ↦ ?_))
  · -- constants
    simp only [RingHom.comp_apply]
    rw [show (Ideal.Quotient.mk (datumRelIdealFam O f (Fin 3) n (ftauKBound f n)))
        (MvPolynomial.C r)
        = algebraMap O (DatumFamRing O f (Fin 3) n (ftauKBound f n)) r from rfl,
      show (datumFamSpec (f := f)
          (u := globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
          (v := globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
          (w := globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
            (w.map ψ)) hgu hgm hgv hgwd hgrel)
          (algebraMap O (DatumFamRing O f (Fin 3) n (ftauKBound f n)) r)
        = algebraMap O (HypField K (f.map ψ)) r from
        RingHom.congr_fun (datumFamSpec_comp_algebraMap (f := f) hgu hgm hgv hgwd hgrel) r,
      show (ftauFamSpec hu hne hv hw hbez)
          (algebraMap O (DatumFamRing O f (Fin 3) n (ftauKBound f n)) r)
        = MvPowerSeries.C r from
        RingHom.congr_fun (ftauFamSpec_comp_algebraMap hu hne hv hw hbez) r,
      halg, RingHom.comp_apply, globExpand_algebraMap_base,
      show setYZero (MvPowerSeries.C r) = (MvPowerSeries.C r : MvPowerSeries (Fin n) O)
        from RingHom.congr_fun setYZero_comp_C r,
      show θ (MvPowerSeries.C r) = PowerSeries.C r from RingHom.congr_fun hθC r,
      PowerSeries.map_C]
  · -- coordinates
    obtain ⟨b', var⟩ := p
    simp only [RingHom.comp_apply]
    rcases var with i | i | i
    · rw [datumFamSpec_mk_X_uVar (f := f) hgu hgm hgv hgwd hgrel, ftauFamSpec_mk_X_uVar,
        show globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
            ((globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg b').coeff i)
          = ((globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
              b').map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)).coeff i from
          (Polynomial.coeff_map ..).symm,
        ← map_ftauFamU_globExpand θ hθC hθX hf hsep hm hm₀ hb hfa h2 hyQ hu hne hgτ
          hcerts hcertsg ⟨w, hw⟩ b', Polynomial.coeff_map]
      rfl
    · rw [datumFamSpec_mk_X_vVar (f := f) hgu hgm hgv hgwd hgrel, ftauFamSpec_mk_X_vVar,
        show globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
            ((globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg b').coeff i)
          = ((globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
              b').map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)).coeff i from
          (Polynomial.coeff_map ..).symm,
        ← map_ftauFamV_globExpand θ hθC hθX hf hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw
          hbez hgτ hcerts hcertsg hθ0 b', Polynomial.coeff_map]
      rfl
    · rw [datumFamSpec_mk_X_wVar (f := f) hgu hgm hgv hgwd hgrel, ftauFamSpec_mk_X_wVar,
        show globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
            ((globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
              (w.map ψ) b').coeff i)
          = ((globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
              (w.map ψ) b').map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)).coeff i from
          (Polynomial.coeff_map ..).symm,
        ← map_ftauFamW_globExpand θ hθC hθX hf hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw
          hbez hgτ hcerts hcertsg hθ0 b', Polynomial.coeff_map]
      rfl

include hθC hθX hθ0 halg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw hbez hgτ
  hcerts hcertsg in
/-- **Unit transfer**: an element of the family ring whose per-disk chart-data
specialization is a unit specializes to a unit (a nonzero element) of the function
field. In particular the denominator-avoidance genericity of the per-disk
specialization is inherited by the global one for free. -/
theorem isUnit_datumFamSpec_glob {x : DatumFamRing O f (Fin 3) n (ftauKBound f n)}
    (hx : IsUnit (ftauFamSpec hu hne hv hw hbez x)) :
    IsUnit (datumFamSpec (f := f)
      (u := globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
      (v := globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
      (w := globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg (w.map ψ))
      hgu hgm hgv hgwd hgrel x) := by
  have halign := globExpand_comp_datumFamSpec θ hθC hθX (hbK := hbK) (hfaK := hfaK) hf
    hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw hbez hgτ hcerts hcertsg hθ0 halg hgu hgm hgv
    hgwd hgrel
  have h1 : globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK
      (datumFamSpec (f := f)
        (u := globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
        (v := globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
        (w := globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
          (w.map ψ)) hgu hgm hgv hgwd hgrel x)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.map ψ (θ (setYZero (ftauFamSpec hu hne hv hw hbez x)))) :=
    RingHom.congr_fun halign x
  -- the constant coefficient of the expansion is the `ψ`-image of a unit
  have hccY : MvPowerSeries.constantCoeff (setYZero (ftauFamSpec hu hne hv hw hbez x))
      = MvPowerSeries.constantCoeff (ftauFamSpec hu hne hv hw hbez x) := by
    rw [setYZero_apply]
    exact MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hasSubst_elim_X_zero
      (by rintro (i | i) <;> simp) _
  have hcc : PowerSeries.constantCoeff
        (PowerSeries.map ψ (θ (setYZero (ftauFamSpec hu hne hv hw hbez x))))
      = ψ (MvPowerSeries.constantCoeff (ftauFamSpec hu hne hv hw hbez x)) := by
    rw [show PowerSeries.constantCoeff
          (PowerSeries.map ψ (θ (setYZero (ftauFamSpec hu hne hv hw hbez x))))
        = MvPowerSeries.constantCoeff
            (MvPowerSeries.map ψ (θ (setYZero (ftauFamSpec hu hne hv hw hbez x))))
        from rfl,
      MvPowerSeries.constantCoeff_map,
      show MvPowerSeries.constantCoeff (θ (setYZero (ftauFamSpec hu hne hv hw hbez x)))
        = PowerSeries.constantCoeff (θ (setYZero (ftauFamSpec hu hne hv hw hbez x)))
        from rfl, hθ0, hccY]
  have hccne : PowerSeries.constantCoeff
      (PowerSeries.map ψ (θ (setYZero (ftauFamSpec hu hne hv hw hbez x)))) ≠ 0 := by
    rw [hcc]
    exact (hx.map (MvPowerSeries.constantCoeff :
      MvPowerSeries (Fin n ⊕ Fin n) O →+* O)).map ψ |>.ne_zero
  refine isUnit_iff_ne_zero.mpr fun h0 ↦ ?_
  rw [h0, map_zero] at h1
  exact hccne (by
    rw [show PowerSeries.map ψ (θ (setYZero (ftauFamSpec hu hne hv hw hbez x))) = 0 from
      IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
        (by rw [← h1, map_zero]), map_zero])

end GlobalSpec

section GlobalN

open HypField
open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {K : Type*} [Field K] [CharZero K] [NeZero (2 : K)] {ψ : O →+* K} {n : ℕ}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧} {dτ : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  {Aτ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {aτ bτ : Fin n → O}
  {dg : CantorCertData (HypField K (f.map ψ))}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The canonical global inverse differential matrix** (the `N`/`hN` plumbing of
`thm:omega-prime-global`): given a rational representation `(den, M′)` of the entries of
the differential matrix of the translated formal group law
(`ChabautyColeman.invariantDiffFold_rational`), the inverse differential matrix evaluated
along the chart coordinates is realized by an actual matrix `N` over the function field:
`N` is the matrix inverse of the specialization of `M′` along the global three-block
Mumford datum, and its disk expansion is `(M⁻¹)(ζ(z))` — the hypothesis `hN` of
`ChabautyColeman.globExpand_globOmega`. -/
theorem exists_globN
    {hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)} {hfaK : (f.map ψ).eval (ψ a) ≠ 0}
    [Algebra O (HypField K (f.map ψ))]
    (halg : algebraMap O (HypField K (f.map ψ)) = (algebraMap K (HypField K (f.map ψ))).comp ψ)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hne : uτ.natDegree = n) (hv : vτ.degree < uτ.degree)
    (hw : vτ ^ 2 - f = uτ * w) (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree)
    (hfdegn : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY uτ n).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (haτ : ∀ i, uτ.eval (aτ i) = 0) (hbτ : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m' : Fin n, (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (aτ i - aτ j))
    (hdτ : IsFtauFoldCerts Aτ aτ bτ hu hne hv hw hbez dτ)
    {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (den : List (DatumFamRing O f (Fin 3) n (ftauKBound f n)))
    (hprod : IsUnit (ftauFamSpec hu hne hv hw hbez den.prod))
    (M' : Fin n → Fin n → Localization.Away den.prod)
    (hM' : ∀ i j, (ftauFoldFGL hu hne hv hw hbez hf hfdegn hroot hcc haτ hbτ hdτ hπ hπ0
      hsplit hunit).diffMatrix i j
      = setYZero (IsLocalization.Away.lift (S := Localization.Away den.prod)
          den.prod hprod (M' i j)))
    (ζK : Fin n → K⟦X⟧)
    (hζK : ∀ j : Fin n, ζK j
      = PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))) :
    ∃ NdM N : Matrix (Fin n) (Fin n) (HypField K (f.map ψ)),
      (∀ i j, globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (NdM i j)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (MvPowerSeries.subst ζK
              (((ftauFoldFGL hu hne hv hw hbez hf hfdegn hroot hcc haτ hbτ hdτ hπ hπ0
                hsplit hunit).map ψ).diffMatrix i j)))
      ∧ (∀ i j, globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (N i j)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (MvPowerSeries.subst ζK
              (((ftauFoldFGL hu hne hv hw hbez hf hfdegn hroot hcc haτ hbτ hdτ hπ hπ0
                hsplit hunit).map ψ).diffMatrix⁻¹ i j)))
      ∧ NdM * N = 1
      ∧ ∃ (hgu : ∀ i, (globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ)
            (ψ m₀) dg i).Monic)
          (hgm : ∀ i, (globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ)
            (ψ m₀) dg i).natDegree = n)
          (hgv : ∀ i, (globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ)
            (ψ m₀) dg i).degree < (n : WithBot ℕ))
          (hgwd : ∀ i, (globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ)
            (ψ m₀) dg (w.map ψ) i).degree < ((ftauKBound f n : WithBot ℕ) + 1))
          (hgrel : ∀ i, globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ)
              (ψ m₀) dg i ^ 2 - f.map (algebraMap O (HypField K (f.map ψ)))
            = globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg i
              * globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
                  (w.map ψ) i)
          (hpg : IsUnit (datumFamSpec (f := f)
            (u := globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
            (v := globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg)
            (w := globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)
              dg (w.map ψ)) hgu hgm hgv hgwd hgrel den.prod)),
          ∀ i j, NdM i j = IsLocalization.Away.lift den.prod hpg (M' i j) := by
  classical
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  -- the substitution homomorphism at the disk chart coordinates
  have hcc0 : ∀ j : Fin n, MvPowerSeries.constantCoeff
      (phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j)) = 0 := fun j ↦
    constantCoeff_phiZeta hf hsep hm hm₀ hb hfa h2 hyQ hu hv hdvdτ hgτ hcerts _
  have hζsub : MvPowerSeries.HasSubst
      (fun j : Fin n ↦ phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcc0
  set θ : MvPowerSeries (Fin n) O →+* O⟦X⟧ :=
    (MvPowerSeries.substAlgHom hζsub).toRingHom with hθdef
  have hθapp : ∀ g, θ g = MvPowerSeries.subst
      (fun j : Fin n ↦ phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j)) g :=
    fun g ↦ MvPowerSeries.substAlgHom_apply hζsub g
  have hθC : θ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)
      = PowerSeries.C := by
    refine RingHom.ext fun r ↦ ?_
    rw [RingHom.comp_apply, hθapp, MvPowerSeries.subst_C r]
    rfl
  have hθX : ∀ j : Fin n,
      θ (MvPowerSeries.X j) = phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j) :=
    fun j ↦ by rw [hθapp, MvPowerSeries.subst_X hζsub]
  have hθ0 : ∀ g, PowerSeries.constantCoeff (θ g) = MvPowerSeries.constantCoeff g :=
    fun g ↦ by
      rw [hθapp]
      exact MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hζsub hcc0 g
  have hθX' : ∀ j : Fin n, ∀ hne' : uτ.natDegree = n,
      θ (MvPowerSeries.X j) = phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne'.symm j) :=
    fun j _ ↦ hθX j
  -- the K-side facts and the datumFamSpec side conditions for the global blocks
  have hyQK : (ψ yQ) ^ 2 = (f.map ψ).eval (ψ xQ) := map_sq_eq_eval_map ψ hyQ
  have hsepK : ψ a ≠ ψ xQ := map_ne_of_isUnit_sub ψ hsep
  have hm₀K : (ψ m₀) * (ψ a - ψ xQ) = -(ψ b) - ψ yQ := map_slope ψ hm₀
  have hwK : (vτ.map ψ) ^ 2 - f.map ψ = uτ.map ψ * w.map ψ := by
    have h := congrArg (Polynomial.map ψ) hw
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul] using h
  have hvK : (vτ.map ψ).degree < (uτ.map ψ).degree := by
    refine Polynomial.degree_map_le.trans_lt (hv.trans_eq ?_)
    rw [degree_eq_natDegree hu.ne_zero, degree_eq_natDegree (hu.map ψ).ne_zero, hu.natDegree_map]
  have hneK : (uτ.map ψ).natDegree = n := (hu.natDegree_map ψ).trans hne
  have hcertsg' : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      (uτ.map ψ).natDegree := by
    rwa [hu.natDegree_map ψ]
  have hgu := globFamU_monic hsepK hm₀K hbK hyQK (hu.map ψ) hwK hcertsg'
  have hgm := globFamU_natDegree (hu.map ψ) hcertsg' hneK
  have hgv := globFamV_degree hsepK hm₀K hbK hyQK (hu.map ψ) hvK hwK hcertsg' hneK
  have hkb : ftauKBound ((f.map ψ).map (algebraMap K (HypField K (f.map ψ)))) n
      = ftauKBound f n := by
    rw [ftauKBound, ftauKBound, (hf.map ψ).natDegree_map, hf.natDegree_map]
  have hgwd : ∀ i, (globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)
      dg (w.map ψ) i).degree < ((ftauKBound f n : WithBot ℕ) + 1) := fun i ↦ by
    have h := globFamW_degree hsepK hm₀K hbK hyQK (hu.map ψ) hvK hwK hcertsg' hneK i
    rwa [hkb] at h
  have hgrel : ∀ i, globFamV (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)
        dg i ^ 2 - f.map (algebraMap O (HypField K (f.map ψ)))
      = globFamU (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg i
        * globFamW (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg
            (w.map ψ) i := fun i ↦ by
    rw [halg, ← Polynomial.map_map]
    exact globFamW_sq_sub hsepK hm₀K hbK hyQK (hu.map ψ) hwK hcertsg' i
  -- the localized specialization along the global blocks
  have hprodG := isUnit_datumFamSpec_glob θ hθC hθX' (hbK := hbK) (hfaK := hfaK) hf hsep
    hm hm₀ hb hfa h2 hyQ hu hne hv hw hbez hgτ hcerts hcertsg hθ0 halg hgu hgm hgv hgwd
    hgrel hprod
  set Θ : Localization.Away den.prod →+* HypField K (f.map ψ) :=
    IsLocalization.Away.lift (S := Localization.Away den.prod) den.prod hprodG with hΘdef
  set Λ : Localization.Away den.prod →+* MvPowerSeries (Fin n ⊕ Fin n) O :=
    IsLocalization.Away.lift (S := Localization.Away den.prod) den.prod hprod with hΛdef
  have halignb := globExpand_comp_datumFamSpec θ hθC hθX' (hbK := hbK) (hfaK := hfaK) hf
    hsep hm hm₀ hb hfa h2 hyQ hu hne hv hw hbez hgτ hcerts hcertsg hθ0 halg hgu hgm hgv
    hgwd hgrel
  have hcompΘ : (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK).comp Θ
      = (((((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
          (PowerSeries.map ψ)).comp θ).comp setYZero).comp Λ) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers den.prod) (RingHom.ext fun z ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [hΘdef, hΛdef, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    exact RingHom.congr_fun halignb z
  -- the direct matrix and its expansion identity
  set Φψ := (ftauFoldFGL hu hne hv hw hbez hf hfdegn hroot hcc haτ hbτ hdτ hπ hπ0
    hsplit hunit).map ψ with hΦψdef
  have hζKcc : ∀ j, MvPowerSeries.constantCoeff (ζK j) = 0 := fun j ↦ by
    rw [hζK, show MvPowerSeries.constantCoeff (PowerSeries.map ψ
          (phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j)))
        = MvPowerSeries.constantCoeff (MvPowerSeries.map ψ
          (phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))) from rfl,
      MvPowerSeries.constantCoeff_map,
      show MvPowerSeries.constantCoeff (phiZeta f a b xQ yQ m m₀ uτ vτ d
        (Fin.cast hne.symm j)) = (0 : O) from hcc0 j, map_zero]
  have hζKsub : MvPowerSeries.HasSubst ζK :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hζKcc
  have hNd : ∀ i j, globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (Θ (M' i j))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (MvPowerSeries.subst ζK (Φψ.diffMatrix i j)) := by
    intro i j
    rw [show globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (Θ (M' i j))
        = ((globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK).comp Θ) (M' i j) from rfl,
      hcompΘ]
    simp only [RingHom.comp_apply]
    rw [show setYZero (Λ (M' i j))
        = (ftauFoldFGL hu hne hv hw hbez hf hfdegn hroot hcc haτ hbτ hdτ hπ hπ0
          hsplit hunit).diffMatrix i j from (hM' i j).symm,
      hθapp,
      show PowerSeries.map ψ (MvPowerSeries.subst
          (fun j : Fin n ↦ phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))
          ((ftauFoldFGL hu hne hv hw hbez hf hfdegn hroot hcc haτ hbτ hdτ hπ hπ0
            hsplit hunit).diffMatrix i j))
        = MvPowerSeries.map ψ (MvPowerSeries.subst
          (fun j : Fin n ↦ phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j))
          ((ftauFoldFGL hu hne hv hw hbez hf hfdegn hroot hcc haτ hbτ hdτ hπ hπ0
            hsplit hunit).diffMatrix i j)) from rfl,
      MvPowerSeries.map_subst hζsub, hΦψdef, FormalGroupLaw.diffMatrix_map,
      Matrix.map_apply,
      show (fun j' : Fin n ↦ MvPowerSeries.map ψ
          (phiZeta f a b xQ yQ m m₀ uτ vτ d (Fin.cast hne.symm j'))) = ζK from
        funext fun j' ↦ (hζK j').symm]
  -- invert over the function field
  have hTunit := (Matrix.isUnit_iff_isUnit_det _).mp Φψ.isUnit_diffMatrix
  have hTmul : Φψ.diffMatrix * Φψ.diffMatrix⁻¹ = 1 := Matrix.mul_nonsing_inv _ hTunit
  set σh : MvPowerSeries (Fin n) K →+* FractionRing (PowerSeries K) :=
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
      (MvPowerSeries.substAlgHom hζKsub).toRingHom with hσdef
  have hσapp : ∀ g, σh g = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (MvPowerSeries.subst ζK g) := fun g ↦
    congrArg (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))
      (MvPowerSeries.substAlgHom_apply hζKsub g)
  have hmulσ : Φψ.diffMatrix.map σh * Φψ.diffMatrix⁻¹.map σh = 1 := by
    have h := congrArg (RingHom.mapMatrix (m := Fin n) σh) hTmul
    rwa [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  set NdM : Matrix (Fin n) (Fin n) (HypField K (f.map ψ)) :=
    Matrix.of fun i j ↦ Θ (M' i j) with hNdMdef
  have hE : Function.Injective (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK) :=
    (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK).injective
  have hNdmap : NdM.map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = Φψ.diffMatrix.map σh := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.map_apply, Matrix.map_apply, hNdMdef, Matrix.of_apply, hNd i j, hσapp]
  have hdet : NdM.det ≠ 0 := by
    intro h0
    have h1 : (Φψ.diffMatrix.map σh).det = 0 := by
      rw [← hNdmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    have h2 := congrArg Matrix.det hmulσ
    rw [Matrix.det_mul, h1, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  have hNdunit : IsUnit NdM.det := isUnit_iff_ne_zero.mpr hdet
  have hmulN : NdM * NdM⁻¹ = 1 := Matrix.mul_nonsing_inv _ hNdunit
  have hleft : Φψ.diffMatrix.map σh
      * NdM⁻¹.map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK) = 1 := by
    have h := congrArg
      (RingHom.mapMatrix (m := Fin n) (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)) hmulN
    rwa [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hNdmap] at h
  have hENM : NdM⁻¹.map (globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK)
      = Φψ.diffMatrix⁻¹.map σh :=
    (Matrix.inv_eq_right_inv hleft).symm.trans (Matrix.inv_eq_right_inv hmulσ)
  refine ⟨NdM, NdM⁻¹, fun i j ↦ hNd i j, fun i j ↦ ?_, hmulN,
    ⟨hgu, hgm, hgv, hgwd, hgrel, hprodG, fun i j ↦ rfl⟩⟩
  have h := congrArg (fun M ↦ M i j) hENM
  simp only [Matrix.map_apply] at h
  rw [h, hσapp]

end GlobalN

end ChabautyColeman

end
