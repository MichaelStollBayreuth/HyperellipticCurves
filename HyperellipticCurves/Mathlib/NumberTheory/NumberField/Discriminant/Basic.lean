/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# The sign of the discriminant of a number field

## Main statements

* `NumberField.discr_neg_iff_odd_nrComplexPlaces`: the discriminant is negative iff the number of
  complex places is odd.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

open NumberField.InfinitePlace

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

theorem discr_neg_iff_odd_nrComplexPlaces : discr K < 0 ↔ Odd (nrComplexPlaces K) := by
  rw [← Int.sign_eq_neg_one_iff_neg, sign_discr, neg_one_pow_eq_neg_one_iff_odd (by decide)]

end NumberField
