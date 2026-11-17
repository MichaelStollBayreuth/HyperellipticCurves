/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.WeierstrassEven
public import HyperellipticCurves.Curve.PointValuation
public import HyperellipticCurves.Curve.WeierstrassOrder
public import HyperellipticCurves.Disks.FuncExpansion
public import HyperellipticCurves.Disks.OrdMatchElement
public import HyperellipticCurves.Specialization.CpZeros

import HyperellipticCurves.Archive.Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Specialization of a principal divisor (chart form, generic chart)

The chart-form `thm:spec` strand, on which the main theorems do not depend: the reduction map
is valued in the affine class group, so the specialization theorem they use is the affine
point-sum form (`HyperellipticCurves.Specialization.DiskPointSum` →
`HyperellipticCurves.Specialization.Pointwise`).

The affine (generic-chart) case of the specialization theorem, assembled from the two halves built
separately:

* the **analytic order-matching** (`order_map_funcExpansionGeneric`): the order of the reduced disk
  expansion of `P + Q·y` is the root multiplicity of the reduced norm polynomial `P² - f·Q²`
  (`= ord_{P̄}(h̄) =` the intrinsic `emultiplicity`, `emultiplicity_pointIdeal_element_generic`);
* the **`C_p` zero-count** (`zeros_eq_ord`): over an algebraically closed complete field the total
  multiplicity of the zeros of the expansion in the open disk (the roots of the Weierstrass factor
  `W`) equals the vanishing order of the reduction.

Composing them gives `thm:spec` on the generic chart: `∑_{red P = P̄} ord_P(h) = ord_{P̄}(h̄)`, both
sides equal to `rootMult` of the reduced norm. The file also treats the Weierstrass chart
(`ChabautyColeman.divisor_specialization_weierstrass_intrinsic`); the infinity chart is
`HyperellipticCurves.Archive.SpecializationInf`. The reduction of `C_p`-points to residue points
(the full multi-disk statement) is not part of this chart-form strand.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

section CpZeros

variable {O F : Type*} [CommRing O] [Field F] [Algebra O F] [IsFractionRing O F]

/-- **Zeros with multiplicity over an algebraically closed field.** The total multiplicity of the
roots in `F` of `W` (mapped from `O`) equals `W.natDegree`. Applied to the distinguished Weierstrass
factor, this is the vanishing order of the reduction; combined with
`root_mem_maximalIdeal_of_distinguished` (all roots lie in the open disk `𝔪`) it counts the zeros of
the disk expansion in the open disk over an algebraically closed complete field. -/
theorem finsum_rootMultiplicity_map [IsAlgClosed F] (W : O[X]) :
    ∑ᶠ z : F, rootMultiplicity z (W.map (algebraMap O F)) = W.natDegree := by
  rw [finsum_rootMultiplicity, natDegree_map_eq_of_injective (IsFractionRing.injective O F)]

section BaseChange

variable {O O' F : Type*} [CommRing O] [IsLocalRing O] [CommRing O'] [Nontrivial O']
  [Field F] [Algebra O' F] [IsFractionRing O' F] [IsAlgClosed F]

/-- **Zeros over `C_p` = order of the reduction.** Given a Weierstrass factorization `h = W·u` over
the DVR `O` (where the disk expansion lives) and a base-change ring hom `φ : O → O'` into the ring
of integers of an algebraically closed complete field `F` (e.g. `O' = 𝓞_ℂ_[p]`, `F = ℂ_p`), the
total multiplicity of the zeros of `h` in the open disk (the roots over `F` of the distinguished
factor `W`) equals the vanishing order of the reduction `h̄`.

This is the analytic content of `thm:spec`: over the algebraic closure the disk-expansion zero-count
(the right-hand side `∑ ord_P(h)`) equals `ord_{P̄}(h̄)`. The factorization must be taken over `O`
(a discrete valuation ring, hence `𝔪`-adically complete) — `𝓞_ℂ_[p]` itself is not — so the base
change `φ` is genuinely needed. -/
theorem zeros_eq_ord (φ : O →+* O') {h : O⟦X⟧} {W : O[X]} {u : O⟦X⟧}
    (hfac : h.IsWeierstrassFactorization W u) :
    ∑ᶠ z : F, rootMultiplicity z ((W.map φ).map (algebraMap O' F))
      = (h.map (residue O)).order.toNat := by
  rw [finsum_rootMultiplicity_map, hfac.isDistinguishedAt.monic.natDegree_map]
  nth_rw 1 [← ENat.toNat_natCast W.natDegree]
  rw [PSeries.natDegree_eq_order_map hfac]

end BaseChange

end CpZeros

variable {O O' F : Type*} [CommRing O] [IsLocalRing O] [CommRing O'] [Nontrivial O']
  [Field F] [Algebra O' F] [IsFractionRing O' F] [IsAlgClosed F]

/-- **Specialization of a principal divisor (generic chart, `thm:spec`).** For the generic-disk
expansion of a function `P + Q·y` with a Weierstrass factorization `= W·u` over the DVR `O`, whose
conjugate does not vanish at `(ā, b̄)`, the total multiplicity of the zeros over an algebraically
closed complete field `F` (the roots of `W`, all in the open disk) equals the intrinsic order
`ord_{P̄}(h̄) = rootMult` of the reduced norm polynomial. -/
theorem divisor_specialization_generic (φ : O →+* O') {f P Q : O[X]} {a b : O}
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hconj : residue O (P.eval a - Q.eval a * b) ≠ 0)
    {W : O[X]} {u : O⟦X⟧}
    (hfac : (funcExpansionGeneric f P Q a b).IsWeierstrassFactorization W u) :
    ∑ᶠ z : F, rootMultiplicity z ((W.map φ).map (algebraMap O' F))
      = ((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O a) := by
  rw [zeros_eq_ord φ hfac, order_map_funcExpansionGeneric P Q hb hfa h2 hN hconj,
    ENat.toNat_natCast]

/-- **Specialization (generic chart), intrinsic form.** The `C_p` zero-count of the generic disk
expansion equals the intrinsic order `ord_{P̄}(h̄)`: the multiplicity `emultiplicity(pointIdeal, ·)`
of the reduced point ideal in the principal ideal of the reduced function `P̄ + Q̄·y`.
Unconditional — the reduced function and its conjugate may vanish simultaneously; the common
`(x - ā)`-factor is handled by `order_funcExpansionGeneric_eq_emultiplicity`. -/
theorem divisor_specialization_generic_intrinsic (φ : O →+* O') {f P Q : O[X]} {a b : O}
    [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
    [Fact (Squarefree (f.map (residue O)))]
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    {W : O[X]} {u : O⟦X⟧}
    (hfac : (funcExpansionGeneric f P Q a b).IsWeierstrassFactorization W u) :
    ∑ᶠ z : F, rootMultiplicity z ((W.map φ).map (algebraMap O' F))
      = emultiplicity (pointIdeal (f.map (residue O)) (residue O a) (residue O b))
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))}) := by
  set ρ := residue O with hρ
  have hbρ : (ρ b) ^ 2 = (f.map ρ).eval (ρ a) := by rw [← map_pow, hb, eval_map_apply]
  have hyρ : ρ b ≠ 0 := fun h0 ↦ (hfa.map ρ).ne_zero (by
    rw [← eval_map_apply, ← hbρ, h0]; ring)
  have hnorm : (P.map ρ) ^ 2 - (f.map ρ) * (Q.map ρ) ^ 2 = (P ^ 2 - f * Q ^ 2).map ρ :=
    map_norm_poly ρ f P Q
  have hNρ : (P.map ρ) ^ 2 - (f.map ρ) * (Q.map ρ) ^ 2 ≠ 0 := hnorm ▸ hN
  have hmap : (funcExpansionGeneric f P Q a b).map ρ
      = funcExpansionGeneric (f.map ρ) (P.map ρ) (Q.map ρ) (ρ a) (ρ b) :=
    map_funcExpansionGeneric ρ f P Q a b hfa h2
  have hord := order_funcExpansionGeneric_eq_emultiplicity (P.map ρ) (Q.map ρ) hbρ hyρ hNρ
  have hne : funcExpansionGeneric (f.map ρ) (P.map ρ) (Q.map ρ) (ρ a) (ρ b) ≠ 0 := by
    intro h0
    have hfaρ : IsUnit ((f.map ρ).eval (ρ a)) := by
      rw [eval_map_apply]; exact hfa.map ρ
    have h2ρ : IsUnit (2 : ResidueField O) := isUnit_iff_ne_zero.mpr two_ne_zero
    have hmc := funcExpansionGeneric_mul_conj (P.map ρ) (Q.map ρ) hbρ hfaρ h2ρ
    rw [h0, zero_mul] at hmc
    refine hNρ (taylor_injective (ρ a) ?_)
    rw [map_zero, ← Polynomial.coe_eq_zero_iff]
    exact hmc.symm
  rw [zeros_eq_ord φ hfac, hmap, ← hord]
  exact ENat.natCast_toNat (order_finite_iff_ne_zero.mpr hne).ne

/-- **Specialization (Weierstrass chart), intrinsic form.** The `C_p` zero-count of the Weierstrass
disk expansion equals `ord_{P̄}(h̄) = emultiplicity(pointIdeal, span{P̄ + Q̄·y})`. The individual
Weierstrass order (`order_map_funcExpansionWeierstrass`, from `weierstrassSeries` even) meets the
individual intrinsic order (`emultiplicity_pointIdeal_element_weierstrass_eq`, from the
`star`-symmetry), both equal to `rootMult` of the reduced norm. -/
theorem divisor_specialization_weierstrass_intrinsic (φ : O →+* O') {f P Q : O[X]} {ω : O}
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hω : f.eval ω = 0)
    (hu : IsUnit (f.derivative.eval ω))
    [NeZero (2 : ResidueField O)] [Fact (Odd (f.map (residue O)).natDegree)]
    [Fact (Squarefree (f.map (residue O)))]
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    {W : O[X]} {u : O⟦X⟧}
    (hfac : (funcExpansionWeierstrass P Q hf hdeg hω hu).IsWeierstrassFactorization W u) :
    ∑ᶠ z : F, rootMultiplicity z ((W.map φ).map (algebraMap O' F))
      = emultiplicity (pointIdeal (f.map (residue O)) (residue O ω) 0)
          (Ideal.span {(⟨P.map (residue O), Q.map (residue O)⟩ :
            HypRing (ResidueField O) (f.map (residue O)))}) := by
  set ρ := residue O with hρ
  have hbρ : (0 : ResidueField O) ^ 2 = (f.map ρ).eval (ρ ω) := by
    simp [eval_map_apply, hω]
  set zr : HypRing (ResidueField O) (f.map ρ) := ⟨P.map ρ, Q.map ρ⟩ with hzr
  have hnorm : zr.re ^ 2 - (f.map ρ) * zr.im ^ 2 = (P ^ 2 - f * Q ^ 2).map ρ :=
    map_norm_poly ρ f P Q
  have hNρ : zr.re ^ 2 - (f.map ρ) * zr.im ^ 2 ≠ 0 := hnorm ▸ hN
  rw [zeros_eq_ord φ hfac, order_map_funcExpansionWeierstrass P Q hf hdeg hω hu hN,
    ENat.toNat_natCast,
    emultiplicity_pointIdeal_element_weierstrass_eq hbρ hNρ, hnorm]

end ChabautyColeman
