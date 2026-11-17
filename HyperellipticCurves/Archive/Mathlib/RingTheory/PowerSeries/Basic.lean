/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# `PowerSeries.rescale` and the base ring

## Main statements

* `ChabautyColeman.constantCoeff_rescale`: `rescale c` does not change the constant coefficient.
* `ChabautyColeman.rescale_comp_algebraMap`, `ChabautyColeman.rescale_aeval`: `rescale c` fixes
  the base ring, so it commutes with `aeval` of a polynomial.

Its clients lie in the Archive: the even-part expansion of a curve function at a Weierstrass
point (`HyperellipticCurves.Archive.WeierstrassEven`) and the expansion at infinity
(`HyperellipticCurves.Archive.FuncExpansionInf`), both of which reparametrize a chart by scaling
the uniformizer. The main development parametrizes each residue disk directly.

Auxiliary material for the Archive of the formalization of the Chabauty–Coleman bound for
hyperelliptic curves (the main theorems do not depend on it); upstreaming candidates for
Mathlib.
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

end ChabautyColeman

end
