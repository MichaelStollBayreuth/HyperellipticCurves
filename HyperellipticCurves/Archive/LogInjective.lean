/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.ExpConverge
public import HyperellipticCurves.Log.Analytic.Lam

import HyperellipticCurves.Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Injectivity of the formal and abelian logarithms

The injectivity half of `thm:log-iso`: the formal logarithm is injective on `(pO)ⁿ`
(`ChabautyColeman.FormalGroupLaw.log_injective`, via the formal exponential of
`HyperellipticCurves.Archive.FormalGroupExp` and its convergence from
`HyperellipticCurves.Archive.ExpConverge`), its canonical-scaled-log form
`ChabautyColeman.FormalGroupLaw.evalT_scaledLog_injective`, and its consequence
`ChabautyColeman.Lam_injective` (the abelian logarithm on the kernel of reduction is
injective). The main theorems do not depend on this file: the count uses the logarithm only as
a homomorphism with integral `π`-scaled coefficients
(`ChabautyColeman.FormalGroupLaw.evalT_scaledLog_add`); the per-disk zero count injects rational
points into zeros of the antiderivative via the disk chart bijection, never via `Λ`.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology ChabautyColeman.MvPSeries

namespace ChabautyColeman

namespace FormalGroupLaw

section Helpers

variable {O : Type*} [CommRing O] {ι : Type*} {K : Type*} [CommRing K] {f : O →+* K} {p : ℕ}

variable [Finite ι]

/-- The descent step behind the injectivity half of the logarithm isomorphism: an identity
`Lg ∘ E = X i` over `K` descends to `Hh ∘ HE i = p · X i` over `O`, given the `p`-scalings
`map f (HL j) = rescale p (Lg j)`, `map f (HE i) = rescale p E` and `p · Hh j = HL j`. -/
theorem subst_descent (hf : Function.Injective f)
    {HL HE Hh : ι → MvPowerSeries ι O} {Lg : ι → MvPowerSeries ι K} {E : MvPowerSeries ι K} {i : ι}
    (hHL : ∀ j, MvPowerSeries.map f (HL j) = rescale (fun _ ↦ (p : K)) (Lg j))
    (hHE : MvPowerSeries.map f (HE i) = rescale (fun _ ↦ (p : K)) E)
    (hHh : ∀ j, (p : O) • Hh j = HL j) (hHh0 : ∀ j, constantCoeff (Hh j) = 0)
    (hLg : HasSubst Lg) (hcomp : subst Lg E = X i) :
    subst Hh (HE i) = (p : O) • X i := by
  have hpX : HasSubst (fun j : ι ↦ (p : K) • (X j : MvPowerSeries ι K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hHhs : HasSubst Hh := hasSubst_of_constantCoeff_zero hHh0
  have hmHh : HasSubst (fun j ↦ MvPowerSeries.map f (Hh j)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by rw [constantCoeff_map, hHh0, map_zero]
  apply map_injective_of_injective hf
  calc MvPowerSeries.map f (subst Hh (HE i))
      = subst (fun j ↦ MvPowerSeries.map f (Hh j)) (MvPowerSeries.map f (HE i)) :=
        map_subst hHhs (HE i)
    _ = subst (fun j ↦ MvPowerSeries.map f (Hh j)) (subst (fun j ↦ (p : K) • X j) E) := by
        rw [hHE, rescale_const_eq_subst]
    _ = subst (fun j ↦ (p : K) • MvPowerSeries.map f (Hh j)) E := by
        rw [subst_comp_subst_apply hpX hmHh]
        congr 1; funext j; rw [subst_smul hmHh, subst_X hmHh]
    _ = subst (fun j ↦ MvPowerSeries.map f (HL j)) E := by
        congr 1; funext j; rw [← map_natCast_smul (MvPowerSeries.map f) O K, hHh]
    _ = subst (fun j ↦ subst (fun j ↦ (p : K) • X j) (Lg j)) E := by
        congr 1; funext j; rw [hHL, rescale_const_eq_subst]
    _ = subst (fun j ↦ (p : K) • X j) (subst Lg E) := (subst_comp_subst_apply hLg hpX E).symm
    _ = subst (fun j ↦ (p : K) • X j) (X i) := by rw [hcomp]
    _ = (p : K) • X i := by rw [subst_X hpX]
    _ = MvPowerSeries.map f ((p : O) • X i) := by
        rw [map_natCast_smul (MvPowerSeries.map f) O K, MvPowerSeries.map_X]

end Helpers

section Cancel

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] {ι : Type*} {p : ℕ}

/-- In the unramified setting `𝔪 = pO`, a family decays as soon as its `p`-multiple does. -/
theorem tendsto_cancel_smul {g : (ι →₀ ℕ) → O}
    (hpm : maximalIdeal O = Ideal.span {(p : O)}) (hp0 : (p : O) ≠ 0)
    (hg : Tendsto (fun d ↦ (p : O) * g d) cofinite (𝓝 0)) :
    Tendsto g cofinite (𝓝 0) := by
  rw [(Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff] at hg ⊢
  intro k _
  filter_upwards [hg (k + 1) trivial] with d hd
  rw [hpm, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton] at hd ⊢
  obtain ⟨w, hw⟩ := hd
  exact ⟨w, mul_left_cancel₀ hp0 (by rw [hw, pow_succ]; ring)⟩

end Cancel

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {f : O →+* K} {p : ℕ}

open scoped Classical in
/-- **Injectivity of the formal logarithm** on `(pO)ⁿ` (`p` odd, unramified `𝔪 = pO`).
The `p`-scaled log `HL` (with `f(coeff_d HL) = f(p)^{deg d} · coeff_d Λ`) has injective
evaluation map `y ↦ (evalT y (HL i))ᵢ`; hence `Λ` is injective on `(pO)ⁿ`. -/
theorem log_injective (hram : IsUniformizer (p : O) p 1) (hpe : 1 + 1 < p)
    (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) :
    ∃ HL : ι → MvPowerSeries ι O,
      (∀ i d, f (coeff d (HL i)) = f (p : O) ^ d.degree * coeff d ((Φ.map f).log i)) ∧
      Function.Injective fun y : ι → O ↦ (fun i ↦ evalT y (HL i)) := by
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hram.prime.pos.ne'
  have hp0 : (p : O) ≠ 0 := fun h ↦ hfp (by rw [h, map_zero])
  choose HL hHL_scale hHL_decay using fun i ↦ Φ.exists_integral_scaled_log hram hpe f hfp i
  choose HE hHE_scale hHE_decay using fun i ↦
    Φ.exp_converges hram.prime (by lia) hram.natCast_mem hfp i
  refine ⟨HL, hHL_scale, ?_⟩
  -- each coefficient of `HL` is divisible by `p`
  have hdvd : ∀ i d, (p : O) ∣ coeff d (HL i) := by
    intro i d
    rcases eq_or_ne d 0 with rfl | hd0
    · have : coeff 0 (HL i) = 0 := hf (by
        rw [map_zero, hHL_scale i 0, map_zero Finsupp.degree, pow_zero, one_mul,
          coeff_zero_eq_constantCoeff_apply, (Φ.map f).constantCoeff_log])
      rw [this]; exact dvd_zero _
    · obtain ⟨c, hcmem, hc⟩ := Φ.coeff_log_map_scale hram hpe f hfp i d
      have hpos : 0 < d.degree :=
        Nat.pos_of_ne_zero fun h ↦ hd0 ((Finsupp.degree_eq_zero_iff d).mp h)
      have hvp : 1 ≤ d.degree - 1 * multiplicity p d.degree := by
        lia [Nat.mul_multiplicity_le_of_lt hpe (p := p) d.degree]
      rw [hf ((hHL_scale i d).trans hc)]
      exact (dvd_pow_self _ (by lia)).trans (hram.mem_pow_iff.mp hcmem)
  choose c hc using fun i d ↦ hdvd i d
  set Hh : ι → MvPowerSeries ι O := fun i ↦ (c i : MvPowerSeries ι O) with hHhdef
  have hHh : ∀ i, (p : O) • Hh i = HL i := fun i ↦ by
    ext d; rw [hHhdef]; exact (hc i d).symm
  have hHL0 : ∀ i, constantCoeff (HL i) = 0 := fun i ↦ hf (by
    rw [map_zero, ← coeff_zero_eq_constantCoeff_apply, hHL_scale i 0, map_zero Finsupp.degree,
      pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply, (Φ.map f).constantCoeff_log])
  have hHh0 : ∀ i, constantCoeff (Hh i) = 0 := fun i ↦ by
    have h2 := congrArg (coeff 0) (hHh i)
    rw [MvPowerSeries.coeff_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hHL0 i] at h2
    exact (mul_eq_zero.mp h2).resolve_left hp0
  have hHh_decay : ∀ s, Tendsto (fun d ↦ coeff d (Hh s)) cofinite (𝓝 0) := fun s ↦ by
    refine tendsto_cancel_smul hram.maximalIdeal_eq hp0 ?_
    have heq : (fun d ↦ (p : O) * coeff d (Hh s)) = fun d ↦ coeff d (HL s) := by
      funext d; simp only [← hHh s, MvPowerSeries.coeff_smul]
    rw [heq]; exact hHL_decay s
  have hdescent : ∀ i, subst Hh (HE i) = (p : O) • X i := fun i ↦
    subst_descent hf (fun j ↦ by simpa using map_eq_rescale (hHL_scale j))
      (by simpa using map_eq_rescale (hHE_scale i))
      hHh hHh0 (hasSubst_of_constantCoeff_zero fun s ↦ (Φ.map f).constantCoeff_log s)
      ((Φ.map f).exp_comp_log i)
  have hkey : ∀ (y : ι → O) (i), evalT (fun s ↦ evalT y (Hh s)) (HE i) = (p : O) • y i :=
    fun y i ↦ by
      rw [← evalT_subst y (hasSubst_of_constantCoeff_zero hHh0) (hHE_decay i) hHh_decay,
        hdescent i, evalT_natCast_smul y p (decay_X i), evalT_X]
  intro y y' hyy
  have hHh_eq : ∀ i, evalT y (Hh i) = evalT y' (Hh i) := fun i ↦ by
    have h := congrFun hyy i
    simp only [] at h
    rw [← hHh i, evalT_natCast_smul y p (hHh_decay i),
      evalT_natCast_smul y' p (hHh_decay i), smul_eq_mul, smul_eq_mul] at h
    exact mul_left_cancel₀ hp0 h
  funext i
  have hval : (p : O) • y i = (p : O) • y' i := by
    rw [← hkey y i, ← hkey y' i, funext hHh_eq]
  rw [smul_eq_mul, smul_eq_mul] at hval
  exact mul_left_cancel₀ hp0 hval

/-- **Injectivity of the formal logarithm**, for the canonical scaled log. -/
theorem evalT_scaledLog_injective (Φ : FormalGroupLaw O ι) (hram : IsUniformizer (p : O) p 1)
    (hpe : 1 + 1 < p) (hf : Function.Injective f) (hfp : f (p : O) ≠ 0) :
    Function.Injective
      fun y : ι → O ↦ (fun i ↦ evalT y (Φ.scaledLog hram hpe f hfp i)) := by
  obtain ⟨HL, hsc, hinj⟩ := Φ.log_injective hram hpe hf
  have hEq : Φ.scaledLog hram hpe f hfp = HL :=
    Φ.scaled_log_unique hf (fun i d ↦ Φ.coeff_scaledLog_map hram hpe hfp i d) hsc
  rw [hEq]
  exact hinj

end FormalGroupLaw

section Lam

universe u'

open Polynomial FormalGroupLaw

variable {O : Type u'} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {p : ℕ}

/-- **The abelian logarithm is injective** (the injectivity half of blueprint `def:Lam`,
via the injectivity half of `thm:log-iso`). -/
theorem Lam_injective (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer (p : O) p 1) (hpe : 1 + 1 < p) :
    Function.Injective (Lam hu hne hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe) := by
  intro c c' h
  have hy := (ftauFoldFGL hu hne hv hw hbez hf
      ((hf.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg) hroot hcc ha hbv
      hd hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing hsplit
      hunit).evalT_scaledLog_injective hram hpe
    (FaithfulSMul.algebraMap_injective O (FractionRing O)) _ h
  have hcoords : (J1_equiv_polydisk hu hne hv hw hbez hf hdeg hfdeg hsq c).1
      = (J1_equiv_polydisk hu hne hv hw hbez hf hdeg hfdeg hsq c').1 := by
    funext j
    rw [← kerScaledCoords_spec hu hne hv hw hbez hf hdeg hfdeg hsq hram c j,
      ← kerScaledCoords_spec hu hne hv hw hbez hf hdeg hfdeg hsq hram c' j, hy]
  exact (J1_equiv_polydisk hu hne hv hw hbez hf hdeg hfdeg hsq).injective
    (Subtype.ext hcoords)

end Lam

end ChabautyColeman

end
