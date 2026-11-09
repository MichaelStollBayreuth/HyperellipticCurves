/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.BaseChangeContraction
public import HyperellipticCurves.Curve.BaseChange

import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# The Galois action on the base-changed coordinate ring

The finite-Galois (Hilbert-90) route to base-change injectivity
(`ChabautyColeman.hypJac_map_injective_of_isGalois`). Injectivity for arbitrary field
extensions is the unconditional `ChabautyColeman.hypJac_map_injective`
(`HyperellipticCurves.Archive.BaseChangeInjectivity`); the main theorems use neither.

A `K`-automorphism `σ` of `K'` acts on `A_{K'}` componentwise on all polynomial
coefficients (`ChabautyColeman.HypRing.galAct`); the action fixes the image of `A_K`
and therefore stabilizes extended ideals. Consequently, if `I·A_{K'} = (h)` is
principal, then `σ(h) = c_σ · h` for a constant `c_σ ∈ K'ˣ`
(`ChabautyColeman.HypRing.exists_unit_galAct_eq`) — the units of the coordinate ring
being the constants. This is the cocycle entering the Hilbert-90 argument for
base-change injectivity. For finite Galois extensions, elements fixed by the full
action lie in the image of `A_K`
(`ChabautyColeman.HypRing.exists_algebraMap_eq_of_forall_galAct`).

Blueprint nodes: `lem:basechange-galact`, `lem:basechange-fixed`.
-/

@[expose] public section

open Polynomial groupCohomology

namespace ChabautyColeman

namespace HypRing

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (f : K[X])

lemma map_comp_algebraMap (σ : K' ≃ₐ[K] K') :
    Polynomial.mapRingHom (σ : K' →+* K') (f.map (algebraMap K K'))
      = f.map (algebraMap K K') := by
  rw [Polynomial.coe_mapRingHom, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun k ↦ σ.commutes k

/-- The action of a `K`-automorphism of `K'` on the base-changed coordinate ring,
componentwise on all polynomial coefficients. -/
noncomputable def galAct (σ : K' ≃ₐ[K] K') :
    HypRing K' (f.map (algebraMap K K')) →+* HypRing K' (f.map (algebraMap K K')) :=
  QuadraticAlgebra.mapRingHomTo (Polynomial.mapRingHom (σ : K' →+* K'))
    (map_comp_algebraMap f σ) (map_zero _)

@[simp]
lemma re_galAct (σ : K' ≃ₐ[K] K') (z : HypRing K' (f.map (algebraMap K K'))) :
    (galAct f σ z).re = z.re.map (σ : K' →+* K') := rfl

@[simp]
lemma im_galAct (σ : K' ≃ₐ[K] K') (z : HypRing K' (f.map (algebraMap K K'))) :
    (galAct f σ z).im = z.im.map (σ : K' →+* K') := rfl

/-- The Galois action fixes the coordinate ring of the base field. -/
theorem galAct_algebraMap (σ : K' ≃ₐ[K] K') (a : HypRing K f) :
    galAct f σ (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) a)
      = algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) a := by
  refine QuadraticAlgebra.ext ?_ ?_
  · rw [re_galAct, algebraMap_eq_baseChange, re_baseChange, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun k ↦ σ.commutes k
  · rw [im_galAct, algebraMap_eq_baseChange, im_baseChange, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun k ↦ σ.commutes k

theorem galAct_galAct (σ τ : K' ≃ₐ[K] K') (z : HypRing K' (f.map (algebraMap K K'))) :
    galAct f σ (galAct f τ z) = galAct f (τ.trans σ) z := by
  refine QuadraticAlgebra.ext ?_ ?_ <;> simp [Polynomial.map_map]

/-- Extended ideals are stable under the Galois action. -/
theorem map_galAct_map_algebraMap (σ : K' ≃ₐ[K] K') (I : Ideal (HypRing K f)) :
    (I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))).map (galAct f σ)
      = I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun a ↦ galAct_algebraMap f σ a

/-- The cocycle attached to a principal extended ideal: if `I·A_{K'} = (h)`, the Galois
action moves the generator by a constant, `σ(h) = c_σ · h` with `c_σ ∈ K'ˣ`
(using that the units of the coordinate ring are the constants). -/
theorem exists_unit_galAct_eq [Fact (Odd f.natDegree)] (σ : K' ≃ₐ[K] K')
    {I : Ideal (HypRing K f)} {h : HypRing K' (f.map (algebraMap K K'))}
    (hspan : I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))
      = Ideal.span {h}) :
    ∃ c : K'ˣ, galAct f σ h
      = algebraMap K' (HypRing K' (f.map (algebraMap K K'))) c * h := by
  have h1 : Ideal.span {galAct f σ h} = Ideal.span {h} := by
    calc Ideal.span {galAct f σ h}
        = (Ideal.span {h}).map (galAct f σ) := by rw [Ideal.map_span, Set.image_singleton]
      _ = ((I.map (algebraMap (HypRing K f)
            (HypRing K' (f.map (algebraMap K K'))))).map (galAct f σ)) := by rw [hspan]
      _ = I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))) :=
          map_galAct_map_algebraMap f σ I
      _ = Ideal.span {h} := hspan
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h1
  have hOdd : Odd (f.map (algebraMap K K')).natDegree := Fact.out
  obtain ⟨c, hc⟩ := (isUnit_iff hOdd).mp (u⁻¹).isUnit
  refine ⟨c, ?_⟩
  have h2 := congrArg (· * (↑u⁻¹ : HypRing K' (f.map (algebraMap K K')))) hu
  simp only [Units.mul_inv_cancel_right] at h2
  rw [h2, ← hc, mul_comm]

/-! ### Fixed-point descent (blueprint node `lem:basechange-fixed`)

For a finite Galois extension `K ⊆ K'`, elements of `A_{K'}` fixed by the full Galois
action lie in the image of `A_K` — coefficientwise from `(K')^G = K`.
-/

section fixedPoints

variable [FiniteDimensional K K'] [IsGalois K K']

-- polynomials fixed by all of Gal(K'/K) come from K[x]
lemma exists_map_eq_of_forall_map {r : K'[X]}
    (hr : ∀ σ : K' ≃ₐ[K] K', r.map (σ : K' →+* K') = r) :
    ∃ q : K[X], q.map (algebraMap K K') = r := by
  have hcoeff (n : ℕ) : ∃ k : K, algebraMap K K' k = r.coeff n := by
    have hmem : r.coeff n ∈ Set.range (algebraMap K K') := by
      refine (IsGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ ↦ ?_
      have h := congrArg (fun s : K'[X] ↦ s.coeff n) (hr σ)
      simpa using h
    exact hmem
  choose k hk using hcoeff
  refine ⟨r.support.sum fun n ↦ C (k n) * X ^ n, ?_⟩
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, hk]
  exact (as_sum_support_C_mul_X_pow r).symm

/-- Elements of `A_{K'}` fixed by the full Galois action lie in the image of `A_K`. -/
theorem exists_algebraMap_eq_of_forall_galAct {z : HypRing K' (f.map (algebraMap K K'))}
    (hz : ∀ σ : K' ≃ₐ[K] K', galAct f σ z = z) :
    ∃ w : HypRing K f,
      algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))) w = z := by
  obtain ⟨qre, hre⟩ := exists_map_eq_of_forall_map (r := z.re) fun σ ↦ by
    have h := congrArg QuadraticAlgebra.re (hz σ)
    simpa using h
  obtain ⟨qim, him⟩ := exists_map_eq_of_forall_map (r := z.im) fun σ ↦ by
    have h := congrArg QuadraticAlgebra.im (hz σ)
    simpa using h
  refine ⟨⟨qre, qim⟩, ?_⟩
  refine QuadraticAlgebra.ext ?_ ?_ <;>
    simp [algebraMap_eq_baseChange, hre, him]

end fixedPoints

/-! ### The Hilbert-90 layer (blueprint node `lem:basechange-galois`)

Principality descends along finite Galois extensions: the cocycle attached to a
principal extended ideal is a Hilbert-90 coboundary, so the generator can be rescaled
by a constant to a Galois-fixed one, which descends to `A_K`; the contraction identity
then recovers the ideal.
-/

/-- The Galois action on constants. -/
theorem galAct_algebraMap_base (σ : K' ≃ₐ[K] K') (x : K') :
    galAct f σ (algebraMap K' (HypRing K' (f.map (algebraMap K K'))) x)
      = algebraMap K' (HypRing K' (f.map (algebraMap K K'))) (σ x) := by
  refine QuadraticAlgebra.ext ?_ ?_ <;> simp

variable [Fact (Odd f.natDegree)] [FiniteDimensional K K'] [IsGalois K K']

/-- Principality descends along a finite Galois extension: an ideal of `A_K` whose
extension to `A_{K'}` is principal is itself principal. This is the Hilbert-90 step. -/
theorem isPrincipal_of_map_isPrincipal (I : Ideal (HypRing K f))
    (hprin : (I.map (algebraMap (HypRing K f)
      (HypRing K' (f.map (algebraMap K K'))))).IsPrincipal) :
    I.IsPrincipal := by
  rcases eq_or_ne I ⊥ with rfl | hI0
  · exact ⟨0, by simp⟩
  obtain ⟨h, hh₀⟩ := Submodule.IsPrincipal.principal
    (I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K')))))
  have hh : I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))
      = Ideal.span {h} := hh₀
  have hne : h ≠ 0 := by
    rintro rfl
    refine hI0 ((Ideal.map_eq_bot_iff_of_injective
      (algebraMap_baseChange_injective (K' := K') f)).mp ?_)
    rw [hh]
    simp
  have hK'inj : Function.Injective
      (algebraMap K' (HypRing K' (f.map (algebraMap K K')))) := RingHom.injective _
  -- the cocycle
  choose c hc using fun σ : K' ≃ₐ[K] K' ↦ exists_unit_galAct_eq f σ hh
  have hcocycle : IsMulCocycle₁ c := by
    intro σ τ
    have hA : galAct f (σ * τ) h
        = algebraMap K' (HypRing K' (f.map (algebraMap K K'))) (c (σ * τ)) * h := hc _
    have hB : galAct f (σ * τ) h
        = algebraMap K' (HypRing K' (f.map (algebraMap K K'))) (σ (c τ) * c σ) * h := by
      have h1 : galAct f (σ * τ) h = galAct f σ (galAct f τ h) :=
        (galAct_galAct f σ τ h).symm
      rw [h1, hc τ, map_mul, galAct_algebraMap_base, hc σ, map_mul]
      ring
    have h2 := mul_right_cancel₀ hne (hA.symm.trans hB)
    exact Units.ext (hK'inj h2)
  -- Hilbert 90
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units c hcocycle
  -- the rescaled generator is Galois-fixed
  set h' := algebraMap K' (HypRing K' (f.map (algebraMap K K'))) (↑β⁻¹ : K') * h with hh'
  have hfix (σ : K' ≃ₐ[K] K') : galAct f σ h' = h' := by
    have hcσ : (c σ : K') = σ β * (↑β⁻¹ : K') := by
      have := hβ σ
      rw [AlgEquiv.smul_units_def] at this
      have hval := congrArg Units.val this
      simpa [Units.val_div_eq_div_val, div_eq_mul_inv] using hval.symm
    rw [hh', map_mul, galAct_algebraMap_base, hc σ, hcσ, map_mul]
    have hone : σ (↑β⁻¹ : K') * σ (↑β : K') = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : algebraMap K' (HypRing K' (f.map (algebraMap K K'))) (σ (↑β⁻¹ : K'))
        * algebraMap K' (HypRing K' (f.map (algebraMap K K'))) (σ (↑β : K')) = 1 := by
      rw [← map_mul, hone, map_one]
    linear_combination (algebraMap K' (HypRing K' (f.map (algebraMap K K')))
      (↑β⁻¹ : K') * h) * h2
  obtain ⟨w, hw⟩ := exists_algebraMap_eq_of_forall_galAct f hfix
  -- contract
  refine ⟨w, ?_⟩
  change I = Ideal.span {w}
  have hspan' : I.map (algebraMap (HypRing K f) (HypRing K' (f.map (algebraMap K K'))))
      = Ideal.span {h'} := by
    rw [hh]
    refine Ideal.span_singleton_eq_span_singleton.mpr ?_
    exact ⟨Units.map (algebraMap K' (HypRing K' (f.map (algebraMap K K')))).toMonoidHom β⁻¹,
      by rw [hh']; simp [mul_comm]⟩
  have h1 := comap_map_baseChange (K' := K') f (Ideal.span {w})
  have h2 := comap_map_baseChange (K' := K') f I
  rw [← h2, ← h1]
  congr 1
  rw [Ideal.map_span, Set.image_singleton, hw, ← hspan']

end HypRing

open nonZeroDivisors in
/-- Base-change injectivity along finite Galois extensions. -/
theorem hypJac_map_injective_of_isGalois {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (f : K[X]) [NeZero (2 : K)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]
    [NeZero (2 : K')] [Fact (Squarefree (f.map (algebraMap K K')))]
    [FiniteDimensional K K'] [IsGalois K K'] :
    Function.Injective (HypJac.map (K' := K') f) :=
  (hypJac_map_injective_iff f).mpr fun I _ hp ↦ HypRing.isPrincipal_of_map_isPrincipal f I hp

end ChabautyColeman

end
