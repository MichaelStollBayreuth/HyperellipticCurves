/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

/-!
# The order of the reduction of a distinguished polynomial

## Main statements

* `Polynomial.IsDistinguishedAt.order_map_coe`: the reduction of a distinguished polynomial
  modulo the ideal, which is `X ^ natDegree` by `Polynomial.IsDistinguishedAt.map_eq_X_pow`, has
  order equal to its degree as a power series.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

open Polynomial PowerSeries
/-- The reduction of a distinguished polynomial has order equal to its degree — it is
`X ^ natDegree` there. -/
theorem Polynomial.IsDistinguishedAt.order_map_coe {R : Type*} [CommRing R] {W : R[X]}
    {I : Ideal R} (hI : I ≠ ⊤) (hW : W.IsDistinguishedAt I) :
    ((W : PowerSeries R).map (Ideal.Quotient.mk I)).order = W.natDegree := by
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [← Polynomial.polynomial_map_coe, hW.map_eq_X_pow]
  push_cast
  exact PowerSeries.order_X_pow _

end
