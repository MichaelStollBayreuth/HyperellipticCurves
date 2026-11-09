/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.RedJ.Congr
public import HyperellipticCurves.RedJ.Stability

/-!
# Equivariance of the reduction of ideals over the tower

The main theorems do not depend on this file: the pairing `λ` is defined on the kernel `J¹` of
reduction directly, so they need neither the finite-index theorem `thm:J1-index` nor its
Frobenius-equivariance machinery. This file provides the equivariance of `redIdealBar` under a
compatible automorphism pack as reusable API; its consumer is
`HyperellipticCurves.Archive.J1FiniteIndex`. The transport lemmas
`ChabautyColeman.pointIdeal_congr` and `ChabautyColeman.HypJac.congr_aj`, which the main
development uses, are in `HyperellipticCurves.RedJ.Congr`.

For the tower of finite extensions `L : IntermediateField K (AlgebraicClosure K)` over which the
reduction map on the Jacobian is assembled (`HyperellipticCurves.RedJ.Tower`), we show that the
reduction `ChabautyColeman.redIdealBar` of a **split-supported** ideal is *equivariant* under a
compatible pack of ring automorphisms: an automorphism `φ` of the complete DVR `O`, a `φ`-semilinear
automorphism `τ` of the finite extension `L` (i.e. `τ (algebraMap O L a) = algebraMap O L (φ a)`),
and an automorphism `σb` of the residue field of `O` induced by `φ`
(`σb (residue O a) = residue O (φ a)`). Concretely, if `f` is fixed by `φ`, then

  `redIdealBar f L (I.map (HypRing.congr _ τ _)) = (redIdealBar f L I).map (HypRing.congr _ σb _)`

(`ChabautyColeman.redIdealBar_congr`). This is the core of the Frobenius-equivariance of the
reduction map `redJ`.

## Main statements

* `ChabautyColeman.isIntegral_ringEquiv_iff`: a `φ`-semilinear automorphism of `L` preserves
  integrality over `O`.
* `ChabautyColeman.redres_ringEquiv`: reduction to the fixed residue field is `σb`-semilinear
  along `τ`.
* `ChabautyColeman.redIdealBar_congr`: the equivariance of `redIdealBar` on split-supported
  ideals.

The proof of the main result mirrors the base-change stability
`ChabautyColeman.redIdealBar_map_of_splitSupported`: the ideal factors into rational point ideals,
each of which maps to a point ideal whose coordinates are the `σb`-images (via `redres_ringEquiv`)
of the original ones.

NOTE (coercion discipline): all statements spell the ring homomorphism underlying an equivalence
`σ` as the ascription `(σ : A →+* B)`; mixing this with the elaborator-inserted coercion in
`p.map σ`/`I.map σ` produces syntactically different coercion terms whose unification inside the
large `HypRing`/ideal terms does not terminate in reasonable time.
-/

@[expose] public section

open Polynomial IsLocalRing IsDedekindDomain

namespace ChabautyColeman

/-! ### Semilinear residue compatibility -/

section SemilinearRed

universe u

variable (O : Type u) [CommRing O] (L : Type u) [Field L] [Algebra O L]
  (φ : O ≃+* O) (τ : L ≃+* L)

/-- A `φ`-semilinear automorphism of `L` sends elements integral over `O` to integral elements:
if `p` is a monic annihilator of `x`, then `p.map φ` is a monic annihilator of `τ x`. -/
theorem isIntegral_ringEquiv (hτ : ∀ a : O, τ (algebraMap O L a) = algebraMap O L (φ a))
    {x : L} (hx : IsIntegral O x) : IsIntegral O (τ x) := by
  obtain ⟨p, hp, hp0⟩ := hx
  refine ⟨p.map (φ : O →+* O), hp.map _, ?_⟩
  have key : eval₂ (algebraMap O L) (τ x) (p.map (φ : O →+* O))
      = τ (eval₂ (algebraMap O L) x p) := by
    rw [eval₂_map, show (algebraMap O L).comp (φ : O →+* O) = (τ : L →+* L).comp (algebraMap O L)
      from RingHom.ext fun a ↦ (hτ a).symm]
    exact (hom_eval₂ p (algebraMap O L) (τ : L →+* L) x).symm
  rw [key, hp0, map_zero]

/-- A `φ`-semilinear automorphism of `L` preserves integrality over `O` (the reverse direction of
`ChabautyColeman.isIntegral_ringEquiv` applies the latter to `φ.symm` and `τ.symm`). -/
theorem isIntegral_ringEquiv_iff (hτ : ∀ a : O, τ (algebraMap O L a) = algebraMap O L (φ a))
    {x : L} : IsIntegral O (τ x) ↔ IsIntegral O x := by
  refine ⟨fun h ↦ ?_, isIntegral_ringEquiv O L φ τ hτ⟩
  have hτ' (a : O) : τ.symm (algebraMap O L a) = algebraMap O L (φ.symm a) :=
    τ.injective (by rw [τ.apply_symm_apply, hτ (φ.symm a), φ.apply_symm_apply])
  have h' := isIntegral_ringEquiv O L φ.symm τ.symm hτ' h
  rwa [τ.symm_apply_apply] at h'

variable [IsLocalRing O] [IsAlgClosed (ResidueField O)]
  [IsDiscreteValuationRing (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

/-- **Reduction to the fixed residue field is semilinear.** If `τ` is `φ`-semilinear on `L` and
`σb` is induced by `φ` on the residue field of `O`, then `redres O L (τ x) = σb (redres O L x)`.
On integral `x = ↑t`, `τ` restricts to a (local) automorphism `τO` of `O_L`, and the residue-field
identification `integralClosureResidueEquiv` conjugates `ResidueField.map τO` into `σb`. -/
theorem redres_ringEquiv (σb : ResidueField O ≃+* ResidueField O)
    (hτ : ∀ a : O, τ (algebraMap O L a) = algebraMap O L (φ a))
    (hσ : ∀ a : O, σb (residue O a) = residue O (φ a)) (x : L) :
    redres O L (τ x) = σb (redres O L x) := by
  by_cases hx : IsIntegral O x
  · obtain ⟨t, rfl⟩ : ∃ t : integralClosure O L, (t : L) = x := ⟨⟨x, hx⟩, rfl⟩
    let τO : integralClosure O L ≃+* integralClosure O L :=
      RingEquiv.restrict τ (integralClosure O L) (integralClosure O L) fun z ↦ by
        rw [mem_integralClosure_iff, mem_integralClosure_iff, isIntegral_ringEquiv_iff O L φ τ hτ]
    have hτO (s : integralClosure O L) : (τO s : L) = τ (s : L) := rfl
    have : IsLocalHom (τO : integralClosure O L →+* integralClosure O L) :=
      ⟨fun a ha ↦ (MulEquiv.isUnit_map (f := τO)).mp ha⟩
    have hcoe (c : O) : ((algebraMap O (integralClosure O L) c : integralClosure O L) : L)
        = algebraMap O L c :=
      (IsScalarTower.algebraMap_apply O (integralClosure O L) L c).symm
    have hτOa (a : O) : τO (algebraMap O (integralClosure O L) a)
        = algebraMap O (integralClosure O L) (φ a) :=
      Subtype.ext <| by rw [hτO, hcoe, hτ, ← hcoe]
    have key (z : ResidueField O) :
        ResidueField.map (τO : integralClosure O L →+* integralClosure O L)
            (integralClosureResidueEquiv O L z)
          = integralClosureResidueEquiv O L (σb z) := by
      obtain ⟨a, rfl⟩ := residue_surjective z
      rw [integralClosureResidueEquiv_residue, ResidueField.map_residue, hσ a,
        integralClosureResidueEquiv_residue]
      exact congrArg (residue (integralClosure O L)) (hτOa a)
    have hconj : (integralClosureResidueEquiv O L).symm
          (ResidueField.map (τO : integralClosure O L →+* integralClosure O L)
            (residue (integralClosure O L) t))
        = σb ((integralClosureResidueEquiv O L).symm (residue (integralClosure O L) t)) := by
      have h := key ((integralClosureResidueEquiv O L).symm (residue (integralClosure O L) t))
      rw [RingEquiv.apply_symm_apply] at h
      rw [h, RingEquiv.symm_apply_apply]
    rw [← hτO t, redres_coe, redres_coe,
      show residue (integralClosure O L) (τO t)
        = ResidueField.map (τO : integralClosure O L →+* integralClosure O L)
            (residue (integralClosure O L) t) from
        (ResidueField.map_residue (τO : integralClosure O L →+* integralClosure O L) t).symm,
      hconj]
  · rw [redres_of_not_isIntegral O L (fun h ↦ hx ((isIntegral_ringEquiv_iff O L φ τ hτ).mp h)),
      redres_of_not_isIntegral O L hx, map_zero]

end SemilinearRed

/-! ### The transported polynomial indices -/

section MapEquiv

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K] (f : O[X])
  (L : IntermediateField K (AlgebraicClosure K)) (φ : O ≃+* O) (τ : L ≃+* L)

/-- If `φ` fixes `f` and `τ` is `φ`-semilinear, then base-changing `τ` fixes the base change of `f`
to `L`: the base change collapses to `f.map (algebraMap O L)`, on which `τ` acts through `φ`. -/
theorem map_map_ringEquiv_eq (hfφ : f.map (φ : O →+* O) = f)
    (hτ : ∀ a : O, τ (algebraMap O L a) = algebraMap O L (φ a)) :
    ((f.map (algebraMap O K)).map (algebraMap K L)).map (τ : L →+* L)
      = (f.map (algebraMap O K)).map (algebraMap K L) := by
  have hcollapse : (f.map (algebraMap O K)).map (algebraMap K L) = f.map (algebraMap O L) := by
    rw [map_map, ← IsScalarTower.algebraMap_eq O K L]
  rw [hcollapse, map_map, show (τ : L →+* L).comp (algebraMap O L)
      = (algebraMap O L).comp (φ : O →+* O) from RingHom.ext hτ, ← map_map, hfφ]

end MapEquiv

section ResidueEquiv

variable {O : Type*} [CommRing O] [IsLocalRing O] (f : O[X]) (φ : O ≃+* O)
  (σb : ResidueField O ≃+* ResidueField O)

/-- If `φ` fixes `f` and `σb` is induced by `φ` on the residue field, then `σb` fixes the reduction
`f.map (residue O)`. -/
theorem map_residue_ringEquiv_eq (hfφ : f.map (φ : O →+* O) = f)
    (hσ : ∀ a : O, σb (residue O a) = residue O (φ a)) :
    (f.map (residue O)).map (σb : ResidueField O →+* ResidueField O) = f.map (residue O) := by
  rw [map_map, show (σb : ResidueField O →+* ResidueField O).comp (residue O)
      = (residue O).comp (φ : O →+* O) from RingHom.ext hσ, ← map_map, hfφ]

end ResidueEquiv

/-! ### Equivariance of the reduction over the tower -/

section Congr

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)]
  (f : O[X])
  (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
  [Fact (Odd (f.map (algebraMap O K)).natDegree)] [Fact (Squarefree (f.map (algebraMap O K)))]
  (φ : O ≃+* O) (τ : L ≃+* L) (σb : ResidueField O ≃+* ResidueField O)

/-- **Per-point equivariance.** The reduction of the point ideal of `(x, y)`, transported by
`τ`, is the transport by `σb` of its reduction: for an integral `x` the coordinates
`redres O L (τ x)`/`redres O L (τ y)` are the `σb`-images of the original ones
(`ChabautyColeman.redres_ringEquiv`); a non-integral `x` reduces to `∞̄` on both sides. -/
theorem redIdealBar_congr_pointIdeal (hfφ : f.map (φ : O →+* O) = f)
    (hτ : ∀ a : O, τ (algebraMap O L a) = algebraMap O L (φ a))
    (hσ : ∀ a : O, σb (residue O a) = residue O (φ a))
    {x y : L} (hxy : y ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K L)).eval x) :
    redIdealBar f L ((pointIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) x y).map
        (HypRing.congr _ τ (map_map_ringEquiv_eq f L φ τ hfφ hτ) : HypRing L _ →+* HypRing L _))
      = (redIdealBar f L (pointIdeal ((f.map (algebraMap O K)).map (algebraMap K L)) x y)).map
          (HypRing.congr _ σb (map_residue_ringEquiv_eq f φ σb hfφ hσ)
            : HypRing (ResidueField O) _ →+* HypRing (ResidueField O) _) := by
  have heval (p : L[X]) (z : L) : (p.map (τ : L →+* L)).eval (τ z) = τ (p.eval z) := by
    rw [eval_map]; exact eval₂_at_apply (τ : L →+* L) z
  have hτxy : (τ y) ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K L)).eval (τ x) := by
    rw [← map_map_ringEquiv_eq f L φ τ hfφ hτ, heval, ← map_pow, hxy]
  rw [pointIdeal_congr _ τ (map_map_ringEquiv_eq f L φ τ hfφ hτ) x y]
  by_cases hx : IsIntegral O x
  · rw [redIdealBar_pointIdeal f L hτxy (isIntegral_ringEquiv O L φ τ hτ hx),
      redres_ringEquiv O L φ τ σb hτ hσ x, redres_ringEquiv O L φ τ σb hτ hσ y,
      redIdealBar_pointIdeal f L hxy hx,
      pointIdeal_congr _ σb (map_residue_ringEquiv_eq f φ σb hfφ hσ) (redres O L x) (redres O L y)]
  · rw [redIdealBar_pointIdeal_of_not_isIntegral f L hτxy
        (fun h ↦ hx ((isIntegral_ringEquiv_iff O L φ τ hτ).mp h)),
      redIdealBar_pointIdeal_of_not_isIntegral f L hxy hx, Ideal.map_top]

/-- **Equivariance of the reduction of a split-supported ideal** under a compatible pack of
automorphisms `(φ, τ, σb)` fixing `f`: `redIdealBar` commutes with transporting the ideal by
`τ` on the source and by `σb` on the target residue curve. This is the well-definedness core of
the Frobenius-equivariance of `redJ`.

The ideal factors into rational point ideals, and
`ChabautyColeman.redIdealBar_map_eq_map_of_splitSupported` transports the factorisation term by
term; the per-point input is `ChabautyColeman.redIdealBar_congr_pointIdeal`. -/
theorem redIdealBar_congr (hfφ : f.map (φ : O →+* O) = f)
    (hτ : ∀ a : O, τ (algebraMap O L a) = algebraMap O L (φ a))
    (hσ : ∀ a : O, σb (residue O a) = residue O (φ a))
    {I : Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L)))}
    (hI : I ≠ 0) (hs : SplitSupported I) :
    redIdealBar f L (I.map (HypRing.congr _ τ (map_map_ringEquiv_eq f L φ τ hfφ hτ)
        : HypRing L _ →+* HypRing L _))
      = (redIdealBar f L I).map (HypRing.congr _ σb (map_residue_ringEquiv_eq f φ σb hfφ hσ)
          : HypRing (ResidueField O) _ →+* HypRing (ResidueField O) _) := by
  refine redIdealBar_map_eq_map_of_splitSupported f L L _ _
    (fun _ hJ ↦ map_ringEquiv_ne_zero
      (HypRing.congr _ τ (map_map_ringEquiv_eq f L φ τ hfφ hτ)) hJ)
    (fun x y hxy ↦ redIdealBar_congr_pointIdeal f L φ τ σb hfφ hτ hσ hxy) hI hs

end Congr

end ChabautyColeman

end
