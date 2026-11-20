/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.BaseChange

/-!
# Contraction and the Hilbert-90 injectivity criterion

Extension-then-contraction of ideals along `A_K → A_{K'}` is the identity
(`ChabautyColeman.comap_map_baseChange`), via an additive retraction obtained from a `K`-linear
splitting of `K ⊆ K'`, and base-change injectivity of Jacobians is equivalent to principality
descent (`ChabautyColeman.hypJac_map_injective_iff`). These feed the finite-Galois (Hilbert-90)
route to base-change injectivity (`HyperellipticCurves.Archive.GaloisAction`). Injectivity for
arbitrary field extensions is the unconditional `ChabautyColeman.hypJac_map_injective` (see
`HyperellipticCurves.Archive.BaseChangeInjectivity`); the main theorems use neither.

Blueprint nodes: `lem:basechange-crit`, `lem:basechange-contract`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section jac

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (f : K[X])
/-! ### Contraction (blueprint node `lem:basechange-contract`)

Extension followed by contraction of ideals along `A_K → A_{K'}` is the identity; the
proof uses an additive retraction `A_{K'} → A_K` obtained by applying a `K`-linear
splitting of `K ⊆ K'` to all polynomial coefficients (no flatness theory is needed).
-/

section retraction

variable (p : K' →ₗ[K] K)

-- apply `p` to all coefficients
private noncomputable def pMap (r : K'[X]) : K[X] :=
  .ofCoeff (Finsupp.mapRange p (map_zero p) r.coeff)

private lemma coeff_pMap (r : K'[X]) (n : ℕ) : (pMap p r).coeff n = p (r.coeff n) := rfl

private lemma pMap_add (r s : K'[X]) : pMap p (r + s) = pMap p r + pMap p s := by
  ext n
  simp [coeff_pMap]

private lemma pMap_map_mul (q : K[X]) (r : K'[X]) :
    pMap p (q.map (algebraMap K K') * r) = q * pMap p r := by
  ext n
  rw [coeff_pMap, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [coeff_map, coeff_pMap, ← Algebra.smul_def, map_smul, smul_eq_mul]

-- the componentwise retraction on coordinate rings
private noncomputable def piA (z : HypRing K' (f.map (algebraMap K K'))) : HypRing K f :=
  ⟨pMap p z.re, pMap p z.im⟩

private lemma re_piA (z : HypRing K' (f.map (algebraMap K K'))) :
    (piA f p z).re = pMap p z.re := rfl

private lemma im_piA (z : HypRing K' (f.map (algebraMap K K'))) :
    (piA f p z).im = pMap p z.im := rfl

private lemma piA_add (z w : HypRing K' (f.map (algebraMap K K'))) :
    piA f p (z + w) = piA f p z + piA f p w := by
  refine QuadraticAlgebra.ext ?_ ?_
  · simp [piA, pMap_add]
  · simp [piA, pMap_add]

private lemma piA_algebraMap_mul (a : HypRing K f)
    (w : HypRing K' (f.map (algebraMap K K'))) :
    piA f p (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) a * w)
      = a * piA f p w := by
  have hre : (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) a * w).re
      = a.re.map (algebraMap K K') * w.re + (f * a.im).map (algebraMap K K') * w.im := by
    rw [QuadraticAlgebra.re_mul, HypRing.algebraMap_eq_baseChange, HypRing.re_baseChange,
      HypRing.im_baseChange, Polynomial.map_mul]
  have him : (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) a * w).im
      = a.re.map (algebraMap K K') * w.im + a.im.map (algebraMap K K') * w.re := by
    rw [QuadraticAlgebra.im_mul, HypRing.algebraMap_eq_baseChange, HypRing.re_baseChange,
      HypRing.im_baseChange]
    ring
  refine QuadraticAlgebra.ext ?_ ?_
  · rw [re_piA, hre, pMap_add, pMap_map_mul, pMap_map_mul, QuadraticAlgebra.re_mul,
      re_piA, im_piA]
  · rw [im_piA, him, pMap_add, pMap_map_mul, pMap_map_mul, QuadraticAlgebra.im_mul,
      re_piA, im_piA]
    ring

variable (hp : ∀ k : K, p (algebraMap K K' k) = k)

include hp in
private lemma pMap_map (q : K[X]) : pMap p (q.map (algebraMap K K')) = q := by
  ext n
  rw [coeff_pMap, coeff_map]
  exact hp _

include hp in
private lemma piA_algebraMap (a : HypRing K f) :
    piA f p (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) a) = a := by
  refine QuadraticAlgebra.ext ?_ ?_
  · rw [re_piA, HypRing.algebraMap_eq_baseChange, HypRing.re_baseChange, pMap_map p hp]
  · rw [im_piA, HypRing.algebraMap_eq_baseChange, HypRing.im_baseChange, pMap_map p hp]

end retraction

-- a K-linear functional splitting the inclusion K → K'
private lemma exists_retraction :
    ∃ p : K' →ₗ[K] K, ∀ k : K, p (algebraMap K K' k) = k := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (K ∙ (1 : K'))
  set e := LinearEquiv.toSpanNonzeroSingleton K K' 1 one_ne_zero
  refine ⟨e.symm.toLinearMap ∘ₗ Submodule.projectionOnto _ q hq, fun k ↦ ?_⟩
  have h1 : algebraMap K K' k = ↑(e k) := by
    simp [e, LinearEquiv.toSpanNonzeroSingleton, Algebra.algebraMap_eq_smul_one]
  simp [h1, Submodule.projectionOnto_apply_left]

/-- Contraction: extension followed by contraction of ideals along the base change
`A_K → A_{K'}` is the identity. -/
theorem comap_map_baseChange (I : Ideal (HypRing K f)) :
    ((I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))).comap
      (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))) = I := by
  obtain ⟨p, hp⟩ := exists_retraction (K := K) (K' := K')
  refine le_antisymm (fun z hz ↦ ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap] at hz
  have key : ∀ w ∈ I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))),
      ∀ v, piA f p (v * w) ∈ I := by
    intro w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, hi, rfl⟩ v
      rw [mul_comm, piA_algebraMap_mul]
      exact I.mul_mem_right _ hi
    · intro v
      rw [mul_zero]
      have hz0 : pMap p 0 = 0 := by
        ext n
        rw [coeff_pMap, coeff_zero, coeff_zero, map_zero]
      have : piA f p 0 = 0 := QuadraticAlgebra.ext hz0 hz0
      rw [this]
      exact I.zero_mem
    · intro x y _ _ hx hy v
      rw [mul_add, piA_add]
      exact I.add_mem (hx v) (hy v)
    · intro a x _ hx v
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (v * a)
  have h1 := key _ hz 1
  rwa [one_mul, piA_algebraMap f p hp] at h1

variable [Fact (Odd f.natDegree)] [NeZero (2 : K)] [Fact (Squarefree f)] [NeZero (2 : K')]
  [Fact (Squarefree (f.map (algebraMap K K')))]
open nonZeroDivisors in
/-- The base-change map on Jacobians is injective iff principality descends:
an ideal of `A_K` whose extension to `A_{K'}` is principal is itself principal. -/
theorem hypJac_map_injective_iff :
    Function.Injective (HypJac.map (K' := K') f) ↔
      ∀ I : Ideal (HypRing K f), I ∈ (Ideal (HypRing K f))⁰ →
        (I.map (algebraMap (HypRing K f)
          (HypRing K' (f.map (algebraMap K K'))))).IsPrincipal →
        I.IsPrincipal := by
  constructor
  · intro hinj I hI hprin
    have h1 : HypJac.map (K' := K') f (ClassGroup.mk0 ⟨I, hI⟩) = 1 := by
      rw [HypJac.map, ClassGroup.extendedHom_mk0]
      exact (ClassGroup.mk0_eq_one_iff _).mpr hprin
    have h2 : ClassGroup.mk0 ⟨I, hI⟩ = 1 := hinj (by rw [h1, map_one])
    exact (ClassGroup.mk0_eq_one_iff hI).mp h2
  · intro h
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
    rw [HypJac.map, ClassGroup.extendedHom_mk0] at hx
    exact (ClassGroup.mk0_eq_one_iff I.2).mpr (h I.1 I.2 ((ClassGroup.mk0_eq_one_iff _).mp hx))

end jac

end ChabautyColeman

end
