/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# `PowerSeries.rescale` and the base ring

How `rescale c` interacts with the constant coefficient, the base-ring embedding,
polynomial `aeval`, and — for a unit `c` — the order.

Its clients lie in the Archive: the even-part expansion of a curve function at a Weierstrass
point (`HyperellipticCurves.Archive.WeierstrassEven`) and the expansion at infinity
(`HyperellipticCurves.Archive.FuncExpansionInf`), both of which reparametrize a chart by
scaling the uniformizer. The main development parametrizes each residue disk directly.
-/

@[expose] public section

open Polynomial PowerSeries

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

/-- `rescale c` scales the `n`-th coefficient by `cⁿ`, so it leaves the `0`-th alone. -/
theorem constantCoeff_rescale (c : O) (s : O⟦X⟧) :
    constantCoeff (rescale c s) = constantCoeff s := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

/-- `rescale c` is a homomorphism of `O`-algebras; this is what makes it commute with
`aeval` of a polynomial. -/
theorem rescale_comp_algebraMap (c : O) :
    (rescale c : O⟦X⟧ →+* O⟦X⟧).comp (algebraMap O (O⟦X⟧)) = algebraMap O (O⟦X⟧) := by
  refine RingHom.ext fun a ↦ ?_
  rw [RingHom.comp_apply, PowerSeries.algebraMap_eq]
  ext n
  rw [coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h <;> simp [h]

/-- A `rescale` commutes with `aeval` of a polynomial (both fix the base ring). -/
theorem rescale_aeval (c : O) (s : O⟦X⟧) (p : O[X]) :
    rescale c (aeval s p) = aeval (rescale c s) p := by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂, rescale_comp_algebraMap]

/-- `order` is preserved under `rescale` by a unit. -/
theorem order_rescale_of_isUnit {c : O} (hc : IsUnit c) (g : O⟦X⟧) :
    (rescale c g).order = g.order := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  set n := g.order.toNat
  have hgord : g.order = (n : ℕ∞) :=
    (ENat.natCast_toNat (order_finite_iff_ne_zero.mpr hg).ne).symm
  obtain ⟨hc0, hlt⟩ := order_eq_nat.mp hgord
  rw [hgord, order_eq_nat]
  refine ⟨?_, fun i hi ↦ ?_⟩
  · rw [coeff_rescale, ne_eq, (hc.pow n).mul_right_eq_zero]; exact hc0
  · rw [coeff_rescale, hlt i hi, mul_zero]

end ChabautyColeman

end
