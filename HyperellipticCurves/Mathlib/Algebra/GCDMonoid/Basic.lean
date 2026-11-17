/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# The normalized gcd and relatively prime elements

## Main statements

* `gcd_eq_one_iff_isRelPrime`: the normalized gcd of `a` and `b` is `1` if and only if `a` and
  `b` are relatively prime.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- The normalized form of `gcd_isUnit_iff_isRelPrime`. -/
theorem gcd_eq_one_iff_isRelPrime {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]
    {a b : α} : gcd a b = 1 ↔ IsRelPrime a b := by
  rw [← gcd_isUnit_iff_isRelPrime, ← normalize_eq_one, normalize_gcd]
