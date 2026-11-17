/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.Equivariance
public import HyperellipticCurves.Archive.StableSplitting
public import HyperellipticCurves.RedJ.J1
public import Mathlib.GroupTheory.Index

import HyperellipticCurves.Archive.Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# The kernel of reduction has finite index (`thm:J1-index`)

The main theorems do not depend on this file: the pairing `λ` is defined on the kernel `J¹` of
reduction directly (`HyperellipticCurves.Log.Analytic.Lambda`), so the main development does not
extend `λ` to the whole Jacobian and needs no finite-index theorem. The result, with its
Frobenius-fixedness satellite `lem:frobfix-finite`, is a theorem of independent interest.

For the complete-DVR reduction pack of `def:redJ` together with a compatible pack of
automorphisms — `φ` of `O`, `φK` of `K`, `Φ` of the algebraic closure of `K`, and `σb` of
the residue field, all fixing `f` — the reduction map is equivariant on fixed classes
(`ChabautyColeman.redJ_fixed`): the reduced Mumford representative of a `φK`-fixed class
is `φK`-fixed, its splitting field `L = K(roots of u)` is `Φ`-stable, and the reduction of
its Mumford ideal transports along the induced automorphisms
(`ChabautyColeman.redIdealBar_congr`).

Consequently, for an arithmetic base field `K₀ ⊆ K` fixed by `φK` and a curve defined
over `K₀`, the classes coming from `J(K₀)` are `φK`-fixed
(`ChabautyColeman.congr_mapBase`), so the image of the composed reduction
`J(K₀) → J(K) → J(κ̄)` consists of `σb`-fixed classes; if `σb` has only finitely many
fixed elements (the Frobenius on `𝔽̄_q`), this image is finite by
`ChabautyColeman.frobFixed_finite`, and the kernel `ChabautyColeman.J1` of the reduction
has finite index in `J(K₀)` (`ChabautyColeman.J1_finiteIndex`).

The intended instantiation is `K₀ = ℚ`, `O = W(𝔽̄_p)` with the Witt Frobenius.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-! ### Base change of a Mumford class -/

section MumfordMap

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {g : K[X]}
  [NeZero (2 : K)] [Fact (Odd g.natDegree)] [Fact (Squarefree g)]
  [NeZero (2 : K')] [Fact (Odd (g.map (algebraMap K K')).natDegree)]
  [Fact (Squarefree (g.map (algebraMap K K')))]

/-- Base change of a Mumford class is the Mumford class of the base-changed data. -/
theorem HypJac.map_mk0_mumfordIdeal {u : K[X]} (hm : u.Monic) (v : K[X]) :
    HypJac.map g (ClassGroup.mk0
        ⟨mumfordIdeal g u v, mumfordIdeal_mem_nonZeroDivisors g hm.ne_zero v⟩)
      = ClassGroup.mk0 ⟨mumfordIdeal (g.map (algebraMap K K'))
          (u.map (algebraMap K K')) (v.map (algebraMap K K')),
          mumfordIdeal_mem_nonZeroDivisors _ (hm.map (algebraMap K K')).ne_zero _⟩ := by
  rw [HypJac.map, ClassGroup.extendedHom_mk0]
  congr 1
  ext : 1
  exact mumfordIdeal_map g u v

end MumfordMap

/-! ### K-level fixedness of the base-changed polynomial -/

section KLevel

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K]
  (f : O[X]) (φ : O ≃+* O) (φK : K ≃+* K)

theorem map_algebraMap_ringEquiv_eq
    (hφK : ∀ a : O, φK (algebraMap O K a) = algebraMap O K (φ a))
    (hfφ : f.map (φ : O →+* O) = f) :
    (f.map (algebraMap O K)).map (φK : K →+* K) = f.map (algebraMap O K) := by
  rw [Polynomial.map_map, show (φK : K →+* K).comp (algebraMap O K)
      = (algebraMap O K).comp (φ : O →+* O) from RingHom.ext hφK, ← Polynomial.map_map, hfφ]

end KLevel

/-! ### Frobenius-fixed classes are few -/

section frobFixed

variable {K : Type*} [Field K] {f : K[X]} [NeZero (2 : K)] [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]

/-- The reduced Mumford data of a `σ`-fixed class is `σ`-fixed (by uniqueness of the
reduced representative). -/
theorem reduced_data_map_eq_of_congr_eq (σ : K ≃+* K) (hf : f.map (σ : K →+* K) = f)
    {c : HypJac K f} {u v : K[X]} (hm : u.Monic) (hdeg : v.degree < u.degree)
    (hred : 2 * u.natDegree < f.natDegree) (hdvd : u ∣ v ^ 2 - f)
    (heq : c = ClassGroup.mk0
      ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hm.ne_zero v⟩)
    (hc : HypJac.congr f σ hf c = c) :
    u.map (σ : K →+* K) = u ∧ v.map (σ : K →+* K) = v := by
  have h1 : HypJac.congr f σ hf c = ClassGroup.mk0
      ⟨mumfordIdeal f (u.map (σ : K →+* K)) (v.map (σ : K →+* K)),
        mumfordIdeal_mem_nonZeroDivisors f (hm.map (σ : K →+* K)).ne_zero
          (v.map (σ : K →+* K))⟩ :=
    (congrArg (HypJac.congr f σ hf) heq).trans (HypJac.congr_mk0_mumfordIdeal f σ hf hm v)
  exact mumfordIdeal_reduced_unique f (hm.map (σ : K →+* K)) hm
    (by rw [degree_map, degree_map]; exact hdeg)
    hdeg
    (by rw [natDegree_map]; exact hred)
    hred
    (by simpa [Polynomial.map_pow, hf] using Polynomial.map_dvd (σ : K →+* K) hdvd)
    hdvd
    (h1.symm.trans (hc.trans heq))

/-- **Fixed classes are few** (`lem:frobfix-finite`): if `σ` is an automorphism of `K`
with finitely many fixed elements and `σ` fixes `f`, then the `σ`-fixed subgroup of `J(K)`
is finite: a fixed class has `σ`-fixed unique reduced Mumford representative, hence data
`(u, v)` with coefficients in the fixed field, of which there are finitely many. -/
theorem frobFixed_finite (σ : K ≃+* K) (hf : f.map (σ : K →+* K) = f)
    (hfix : {x : K | σ x = x}.Finite) :
    {c : HypJac K f | HypJac.congr f σ hf c = c}.Finite := by
  classical
  choose u v hm hdeg hred hdvd heq using exists_mk0_mumfordIdeal_reduced (f := f)
  have hP : {p : K[X] | p.natDegree ≤ f.natDegree / 2
      ∧ ∀ i, p.coeff i ∈ {x : K | σ x = x}}.Finite :=
    Polynomial.finite_setOf_natDegree_le_of_coeff_mem hfix _
  refine Set.Finite.of_finite_image (f := fun c ↦ (u c, v c)) ((hP.prod hP).subset ?_)
    fun c _ d _ h ↦ ?_
  · rintro - ⟨c, hc, rfl⟩
    -- `σ` fixes the reduced data of a fixed class
    have hσc := reduced_data_map_eq_of_congr_eq σ hf (hm c) (hdeg c) (hred c) (hdvd c)
      (heq c) hc
    refine ⟨⟨by have := hred c; lia, fun i ↦ ?_⟩, ⟨?_, fun i ↦ ?_⟩⟩
    · simpa [coeff_map] using congrArg (fun p ↦ p.coeff i) hσc.1
    · exact (natDegree_le_natDegree (hdeg c).le).trans (by have := hred c; lia)
    · simpa [coeff_map] using congrArg (fun p ↦ p.coeff i) hσc.2
  · -- the reduced data determine the class
    simp only [Prod.mk.injEq] at h
    exact (heq c).trans ((congrArg ClassGroup.mk0
      (Subtype.ext (congrArg₂ (mumfordIdeal f) h.1 h.2))).trans (heq d).symm)

end frobFixed

/-! ### redJ maps fixed classes to fixed classes -/

section RedJFixed

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  {f : O[X]}
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  (φ : O ≃+* O) (φK : K ≃+* K) (σb : ResidueField O ≃+* ResidueField O)
  (Φ : AlgebraicClosure K ≃+* AlgebraicClosure K)

/-- **The reduction of a fixed class is fixed**: for a compatible pack of automorphisms
(`φ` of `O`, `φK` of `K`, `Φ` of the algebraic closure, `σb` of the residue field) fixing
`f`, the reduction `redJ` maps `φK`-fixed classes to `σb`-fixed classes. -/
theorem redJ_fixed (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hφK : ∀ a : O, φK (algebraMap O K a) = algebraMap O K (φ a))
    (hσ : ∀ a : O, σb (residue O a) = residue O (φ a))
    (hΦ : ∀ x : K, Φ (algebraMap K (AlgebraicClosure K) x)
      = algebraMap K (AlgebraicClosure K) (φK x))
    (hfφ : f.map (φ : O →+* O) = f)
    {c : HypJac K (f.map (algebraMap O K))}
    (hc : HypJac.congr (f.map (algebraMap O K)) φK
      (map_algebraMap_ringEquiv_eq f φ φK hφK hfφ) c = c) :
    HypJac.congr (f.map (residue O)) σb (map_residue_ringEquiv_eq f φ σb hfφ hσ)
        (redJ c)
      = redJ c := by
  classical
  -- the reduced Mumford data of `c` is `φK`-fixed
  obtain ⟨u, v, hm, hdeg', hred, hdvd, heq⟩ :=
    exists_mk0_mumfordIdeal_reduced (f.map (algebraMap O K)) c
  obtain ⟨huφ, hvφ⟩ := reduced_data_map_eq_of_congr_eq φK
    (map_algebraMap_ringEquiv_eq f φ φK hφK hfφ) hm hdeg' hred hdvd heq hc
  -- the stable splitting field of `u` and the restricted automorphism
  set L := IntermediateField.adjoin K (u.rootSet (AlgebraicClosure K)) with hLdef
  have : FiniteDimensional K L := finiteDimensional_adjoin_rootSet u
  set τ := adjoinRootSetEquiv φK Φ hΦ huφ with hτdef
  have hτK (x : K) : τ (algebraMap K L x) = algebraMap K L (φK x) :=
    adjoinRootSetEquiv_algebraMap φK Φ hΦ huφ x
  have hτO (a : O) : τ (algebraMap O L a) = algebraMap O L (φ a) := by
    have h1 : algebraMap O L a = algebraMap K L (algebraMap O K a) := rfl
    have h2 : algebraMap O L (φ a) = algebraMap K L (algebraMap O K (φ a)) := rfl
    rw [h1, h2, hτK, hφK]
  have hcomp : (τ : L →+* L).comp (algebraMap K L)
      = (algebraMap K L).comp (φK : K →+* K) := RingHom.ext hτK
  have hmapτ (p : K[X]) (hp : p.map (φK : K →+* K) = p) :
      (p.map (algebraMap K L)).map (τ : L →+* L) = p.map (algebraMap K L) := by
    rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hp]
  -- the Mumford ideal of the data over `L`
  set uL := u.map (algebraMap K L) with huLdef
  set vL := v.map (algebraMap K L) with hvLdef
  have huL : uL ≠ 0 := (hm.map (algebraMap K L)).ne_zero
  have hdvdL : uL ∣ vL ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L) := by
    have h := Polynomial.map_dvd (algebraMap K L) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow] at h
  set M := mumfordIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) uL vL with hMdef
  have hM0 : M ≠ 0 := by
    simpa [Submodule.zero_eq_bot] using
      mumfordIdeal_ne_bot ((f.map (algebraMap O K)).map (algebraMap K L)) huL vL
  have hs : SplitSupported M :=
    splitSupported_mumfordIdeal huL hdvdL (splits_map_adjoin_rootSet u)
  -- `redJ c` is the class of the reduction of `M`
  have hpair : IsRedJPair c (ClassGroup.mk0 ⟨redIdealBar f L M,
      mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L M)⟩) := by
    refine ⟨L, inferInstance, ⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, hs, ?_, rfl⟩
    rw [heq]
    exact HypJac.map_mk0_mumfordIdeal hm v
  rw [IsRedJPair.redJ_eq hf hdeg hpair]
  -- `M` is `τ`-fixed
  have hMτ : M.map (HypRing.congr _ τ (map_map_ringEquiv_eq f L φ τ hfφ hτO)
      : HypRing L _ →+* HypRing L _) = M := by
    rw [hMdef, mumfordIdeal_congr, hmapτ u huφ, hmapτ v hvφ]
  -- transport the reduction
  have hval : (redIdealBar f L M).map
      (HypRing.congr _ σb (map_residue_ringEquiv_eq f φ σb hfφ hσ)
        : HypRing (ResidueField O) _ →+* HypRing (ResidueField O) _) = redIdealBar f L M := by
    rw [← redIdealBar_congr f L φ τ σb hfφ hτO hσ hM0 hs, hMτ]
  exact (ClassGroup.mulEquiv_mk0 _ _).trans (congrArg ClassGroup.mk0 (Subtype.ext hval))

end RedJFixed

/-! ### Fixedness of base-changed classes -/

section Base

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K]
  {f : O[X]} (K₀ : Type*) [Field K₀] [Algebra K₀ K] (f₀ : K₀[X])
  [CharZero K] [CharZero K₀]
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd f₀.natDegree)] [Fact (Squarefree f₀)]

/-- Base-changed classes are fixed by an automorphism of `K` that fixes `K₀`. -/
theorem congr_mapBase (φ : O ≃+* O) (φK : K ≃+* K)
    (hφK : ∀ a : O, φK (algebraMap O K a) = algebraMap O K (φ a))
    (hfφ : f.map (φ : O →+* O) = f)
    (hφK₀ : ∀ x : K₀, φK (algebraMap K₀ K x) = algebraMap K₀ K x)
    (hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)) (c₀ : HypJac K₀ f₀) :
    HypJac.congr (f.map (algebraMap O K)) φK (map_algebraMap_ringEquiv_eq f φ φK hφK hfφ)
        (mapBase K₀ f₀ hf₀ c₀)
      = mapBase K₀ f₀ hf₀ c₀ := by
  classical
  obtain ⟨u₀, v₀, hm₀, hdeg₀, hred₀, hdvd₀, heq₀⟩ := exists_mk0_mumfordIdeal_reduced f₀ c₀
  have hfixp (p : K₀[X]) : (p.map (algebraMap K₀ K)).map (φK : K →+* K)
      = p.map (algebraMap K₀ K) := by
    rw [Polynomial.map_map, show (φK : K →+* K).comp (algebraMap K₀ K) = algebraMap K₀ K
      from RingHom.ext hφK₀]
  -- the image class is a Mumford class with data from `K₀`
  have h1 : HypJac.map f₀ c₀ = ClassGroup.mk0
      ⟨mumfordIdeal (f₀.map (algebraMap K₀ K)) (u₀.map (algebraMap K₀ K))
        (v₀.map (algebraMap K₀ K)),
        mumfordIdeal_mem_nonZeroDivisors _ (hm₀.map (algebraMap K₀ K)).ne_zero _⟩ := by
    rw [heq₀]
    exact HypJac.map_mk0_mumfordIdeal hm₀ v₀
  have h2 : mapBase K₀ f₀ hf₀ c₀ = ClassGroup.mk0
      ⟨mumfordIdeal (f.map (algebraMap O K)) (u₀.map (algebraMap K₀ K))
        (v₀.map (algebraMap K₀ K)),
        mumfordIdeal_mem_nonZeroDivisors _ (hm₀.map (algebraMap K₀ K)).ne_zero _⟩ := by
    have h3 : mapBase K₀ f₀ hf₀ c₀ = HypJac.congr (f₀.map (algebraMap K₀ K))
        (RingEquiv.refl K) (map_refl_eq K₀ f₀ hf₀) (HypJac.map f₀ c₀) := rfl
    have hval : mumfordIdeal (f.map (algebraMap O K))
        ((u₀.map (algebraMap K₀ K)).map ((RingEquiv.refl K : K ≃+* K) : K →+* K))
        ((v₀.map (algebraMap K₀ K)).map ((RingEquiv.refl K : K ≃+* K) : K →+* K))
        = mumfordIdeal (f.map (algebraMap O K)) (u₀.map (algebraMap K₀ K))
            (v₀.map (algebraMap K₀ K)) := by
      rw [RingEquiv.toRingHom_refl, Polynomial.map_id, Polynomial.map_id]
    rw [h3, h1]
    exact (HypJac.congr_mk0_mumfordIdeal _ _ _ (hm₀.map (algebraMap K₀ K)) _).trans
      (congrArg ClassGroup.mk0 (Subtype.ext hval))
  have hval2 : mumfordIdeal (f.map (algebraMap O K))
      ((u₀.map (algebraMap K₀ K)).map (φK : K →+* K))
      ((v₀.map (algebraMap K₀ K)).map (φK : K →+* K))
      = mumfordIdeal (f.map (algebraMap O K)) (u₀.map (algebraMap K₀ K))
          (v₀.map (algebraMap K₀ K)) := by
    rw [hfixp u₀, hfixp v₀]
  rw [h2]
  exact (HypJac.congr_mk0_mumfordIdeal _ _ _ (hm₀.map (algebraMap K₀ K)) _).trans
    (congrArg ClassGroup.mk0 (Subtype.ext hval2))

end Base

/-! ### The finite index of the kernel of reduction -/

section J1

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  {f : O[X]}
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  (K₀ : Type*) [Field K₀] [Algebra K₀ K]
  (f₀ : K₀[X]) [Fact (Odd f₀.natDegree)]
  (φ : O ≃+* O) (φK : K ≃+* K) (σb : ResidueField O ≃+* ResidueField O)
  (Φ : AlgebraicClosure K ≃+* AlgebraicClosure K)
  [CharZero K₀] [Fact (Squarefree f₀)]

/-- **The kernel of reduction has finite index** (`thm:J1-index`). -/
theorem J1_finiteIndex (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K))
    (hφK : ∀ a : O, φK (algebraMap O K a) = algebraMap O K (φ a))
    (hσ : ∀ a : O, σb (residue O a) = residue O (φ a))
    (hΦ : ∀ x : K, Φ (algebraMap K (AlgebraicClosure K) x)
      = algebraMap K (AlgebraicClosure K) (φK x))
    (hfφ : f.map (φ : O →+* O) = f)
    (hφK₀ : ∀ x : K₀, φK (algebraMap K₀ K x) = algebraMap K₀ K x)
    (hfix : {x : ResidueField O | σb x = x}.Finite) :
    (J1 K₀ f₀ hf hdeg hf₀).FiniteIndex := by
  set ρ := (redJHom hf hdeg).comp (mapBase K₀ f₀ hf₀) with hρ
  have hsub : Set.range ρ ⊆ {r | HypJac.congr (f.map (residue O)) σb
      (map_residue_ringEquiv_eq f φ σb hfφ hσ) r = r} := by
    rintro - ⟨c₀, rfl⟩
    exact redJ_fixed φ φK σb Φ hf hdeg hφK hσ hΦ hfφ
      (congr_mapBase K₀ f₀ φ φK hφK hfφ hφK₀ hf₀ c₀)
  have hrange : (Set.range ρ).Finite :=
    (frobFixed_finite σb (map_residue_ringEquiv_eq f φ σb hfφ hσ) hfix).subset hsub
  have h1 : Finite ρ.range := by
    have := hrange.to_subtype
    rwa [← MonoidHom.coe_range] at this
  have hker : J1 K₀ f₀ hf hdeg hf₀ = ρ.ker := rfl
  have h2 : Finite (HypJac K₀ f₀ ⧸ J1 K₀ f₀ hf hdeg hf₀) := by
    rw [hker]
    exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

end J1

end ChabautyColeman

end
