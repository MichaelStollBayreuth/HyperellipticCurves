/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.RingTheory.AdicCompletion.Completeness`: the local ring `k⟦X⟧` and
-- its maximal ideal `(X)` (`PowerSeries.maximalIdeal_eq_span_X`), from
-- `Mathlib.RingTheory.PowerSeries.Inverse`.
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# `k⟦X⟧` is complete for its maximal ideal

Mathlib has the completeness of power series for the ideal `(X)`; this restates it for the
maximal ideal of `k⟦X⟧`, which is the form in which a complete local ring is consumed.

## Main statements

* `PowerSeries.instIsAdicCompleteMaximalIdeal`: `k⟦X⟧` is complete for its maximal ideal.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

open IsLocalRing

namespace PowerSeries

variable {k : Type*} [Field k]

/-- `k⟦X⟧` is complete for its maximal ideal `(X)`. -/
instance instIsAdicCompleteMaximalIdeal : IsAdicComplete (maximalIdeal k⟦X⟧) k⟦X⟧ := by
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

end PowerSeries

end
