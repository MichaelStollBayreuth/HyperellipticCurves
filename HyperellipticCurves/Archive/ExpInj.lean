/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Disks.FuncExpansion
public import HyperellipticCurves.RedJ.RedIdealPrincipal

/-!
# Expansion injectivity (blueprint `lem:exp-inj`)

The main theorems do not depend on this file: their identifications compare series through
uniqueness of reduced representatives, and the chart identification lemmas re-derive what they
need at their specific configurations.

A function `P + Q·y` on the hyperelliptic curve `y² = f(x)` (`deg f` odd) is determined
by its full power-series expansion at a single affine non-Weierstrass point
(`ChabautyColeman.funcExpansionGeneric_eq_zero_iff`,
`ChabautyColeman.funcExpansionGeneric_injective`): the expansion times its conjugate is
the Taylor series of the norm polynomial `P² - f·Q²`
(`ChabautyColeman.funcExpansionGeneric_mul_conj`), which vanishes only for `P = Q = 0`
by the degree-parity count (`ChabautyColeman.sq_sub_mul_sq_ne_zero`). Rational functions
and differentials are covered by clearing denominators at the use site (a rational
differential is `(P + Q·y)/(R + S·y)·dx/y` and expansions multiply).
-/

@[expose] public section

open Polynomial PowerSeries

namespace ChabautyColeman

variable {K : Type*} [Field K] [NeZero (2 : K)] {f : K[X]}

/-- **Expansion injectivity** (blueprint `lem:exp-inj`): a function `P + Q·y` on the
curve `y² = f(x)` (`deg f` odd) whose full expansion at an affine non-Weierstrass point
vanishes is zero. -/
theorem funcExpansionGeneric_eq_zero_iff (hodd : Odd f.natDegree) {P Q : K[X]} {a b : K}
    (hb : b ^ 2 = f.eval a) (hfa : f.eval a ≠ 0) :
    funcExpansionGeneric f P Q a b = 0 ↔ P = 0 ∧ Q = 0 := by
  constructor
  · intro h0
    have hconj := funcExpansionGeneric_mul_conj P Q hb (isUnit_iff_ne_zero.mpr hfa)
      (isUnit_iff_ne_zero.mpr (NeZero.ne 2))
    rw [h0, zero_mul] at hconj
    have hpoly : taylor a (P ^ 2 - f * Q ^ 2) = 0 := by
      have h1 : ((taylor a (P ^ 2 - f * Q ^ 2) : K[X]) : K⟦X⟧) = 0 := hconj.symm
      exact_mod_cast h1
    have hnorm : P ^ 2 - f * Q ^ 2 = 0 := taylor_injective a (by rwa [map_zero])
    by_contra hne
    rw [not_and_or] at hne
    exact sq_sub_mul_sq_ne_zero hodd (fun ⟨hP, hQ⟩ ↦ by
      rcases hne with h | h <;> [exact h hP; exact h hQ]) hnorm
  · rintro ⟨rfl, rfl⟩
    rw [funcExpansionGeneric]
    simp

/-- Two functions on the curve with the same full expansion at an affine
non-Weierstrass point are equal. -/
theorem funcExpansionGeneric_injective (hodd : Odd f.natDegree) {P Q P' Q' : K[X]}
    {a b : K} (hb : b ^ 2 = f.eval a) (hfa : f.eval a ≠ 0)
    (h : funcExpansionGeneric f P Q a b = funcExpansionGeneric f P' Q' a b) :
    P = P' ∧ Q = Q' := by
  have hsub : funcExpansionGeneric f (P - P') (Q - Q') a b = 0 := by
    rw [funcExpansionGeneric, map_sub, map_sub, Polynomial.coe_sub, Polynomial.coe_sub]
    rw [funcExpansionGeneric, funcExpansionGeneric] at h
    linear_combination h
  obtain ⟨h1, h2⟩ := (funcExpansionGeneric_eq_zero_iff hodd hb hfa).mp hsub
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

end ChabautyColeman

end
