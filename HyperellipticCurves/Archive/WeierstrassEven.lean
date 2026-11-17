/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Disks.FuncExpansion
public import HyperellipticCurves.Series.HenselRoot

import HyperellipticCurves.Archive.Mathlib.RingTheory.PowerSeries.Basic
import HyperellipticCurves.Archive.Mathlib.RingTheory.PowerSeries.Order

/-!
# Evenness of the Weierstrass series and the individual Weierstrass order

Individual function orders at ramified points are consumed only by the chart-form `thm:spec`
strand (`HyperellipticCurves.Archive.SpecializationGeneric`); the main theorems do not depend on
them, since the point-sum route computes disk sums through the norm decomposition and the
two-to-one parameter fold instead.

The Weierstrass coordinate series `x(z)` is *even* (`x(-z) = x(z)`, i.e. `rescale (-1)` fixes it):
the equation `f(x) = z²` is invariant under `z ↦ -z`, so uniqueness of the Hensel root forces
evenness (`weierstrassSeries_even`, via `hensel_unique` applied over the local ring `O⟦X⟧`).

Consequently the expansion of the conjugate `P - Q·y` is `rescale (-1)` of the expansion of
`P + Q·y` (`funcExpansionWeierstrass_neg`), and `rescale` by a unit preserves `order`
(`order_rescale_of_isUnit`), so the two conjugate reduced orders are equal. Halving the
norm-decomposition sum then gives the *individual* Weierstrass order
(`order_map_funcExpansionWeierstrass`) `= rootMult` of the reduced norm — the analytic
counterpart of `emultiplicity_pointIdeal_element_weierstrass_eq`.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

variable [IsLocalRing O]

/-- The Weierstrass coordinate series is even: `x(-z) = x(z)` (the hyperelliptic involution fixes
the `x`-coordinate). Proved by uniqueness of the Hensel root over the local ring `O⟦X⟧`. -/
theorem weierstrassSeries_even {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    rescale (-1 : O) (weierstrassSeries hf hdeg hω hu) = weierstrassSeries hf hdeg hω hu := by
  set ws := weierstrassSeries hf hdeg hω hu with hws
  set φ : O →+* O⟦X⟧ := algebraMap O (O⟦X⟧) with hφ
  have haev : aeval (rescale (-1 : O) ws) f = PowerSeries.X ^ 2 := by
    rw [← rescale_aeval, weierstrassSeries_eval, map_pow, rescale_X, mul_pow, ← map_pow, neg_one_sq,
      map_one, one_mul]
  refine hensel_unique (f := f.map φ) (x := rescale (-1 : O) ws) (x' := ws) ?_ ?_ ?_
  · rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, map_sub,
      constantCoeff_rescale, sub_self]
    exact not_isUnit_zero
  · rw [derivative_map, eval_map, ← aeval_def]
    exact isUnit_aeval_deriv_weierstrassSeries hf hdeg hω hu
  · rw [eval_map, eval_map, ← aeval_def, ← aeval_def, haev, weierstrassSeries_eval]

/-- The Weierstrass expansion of the conjugate `P - Q·y` is `rescale (-1)` of that of `P + Q·y`
(by evenness of the coordinate series). -/
theorem funcExpansionWeierstrass_neg (P Q : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    funcExpansionWeierstrass P (-Q) hf hdeg hω hu
      = rescale (-1 : O) (funcExpansionWeierstrass P Q hf hdeg hω hu) := by
  rw [funcExpansionWeierstrass, funcExpansionWeierstrass, map_add, map_mul, rescale_aeval,
    rescale_aeval, weierstrassSeries_even, rescale_X, map_neg,
    show (PowerSeries.C (-1 : O) : O⟦X⟧) = -1 from by rw [map_neg, map_one]]
  ring

/-- **Order matching, Weierstrass chart (individual).** The order of the reduced expansion of
`P + Q·y` at a Weierstrass point is `rootMult` of the reduced norm — the two branches
contribute equally because `weierstrassSeries` is even. Matches the generic
`order_map_funcExpansionGeneric`. -/
theorem order_map_funcExpansionWeierstrass (P Q : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0) :
    ((funcExpansionWeierstrass P Q hf hdeg hω hu).map (residue O)).order
      = ((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O ω) := by
  have hsymorder :
      ((funcExpansionWeierstrass P (-Q) hf hdeg hω hu).map (residue O)).order
        = ((funcExpansionWeierstrass P Q hf hdeg hω hu).map (residue O)).order := by
    rw [funcExpansionWeierstrass_neg, ← rescale_map, map_neg, map_one]
    exact order_rescale_of_isUnit isUnit_one.neg _
  have hsum := order_map_funcExpansionWeierstrass_add_conj P Q hf hdeg hω hu hN
  rw [hsymorder] at hsum
  have hrhs : ((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O ω) • (2 : ℕ∞)
      = ((((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O ω) * 2 : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]; push_cast; ring
  have hle : ((funcExpansionWeierstrass P Q hf hdeg hω hu).map (residue O)).order
      ≤ ((((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O ω) * 2 : ℕ) : ℕ∞) := by
    rw [← hrhs, ← hsum]; exact le_self_add
  have hfin := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
  lift ((funcExpansionWeierstrass P Q hf hdeg hω hu).map (residue O)).order to ℕ
    using hfin with m hm
  rw [← Nat.cast_add, hrhs, Nat.cast_inj] at hsum
  rw [Nat.cast_inj]; lia

end ChabautyColeman
