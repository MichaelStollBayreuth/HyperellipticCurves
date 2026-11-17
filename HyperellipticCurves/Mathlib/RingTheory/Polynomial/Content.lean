/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Polynomial.Content

/-!
# The gcd of two polynomials over a field

## Main statements

* `Polynomial.exists_monic_mul_eq_and_isCoprime`: `p = d * p₁` and `q = d * q₁` with `d` monic and
  `p₁` prime to `q₁`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

open Polynomial

namespace Polynomial

/-- `p` and `q ≠ 0` factor as `p = d * p₁` and `q = d * q₁` with `d` monic and `p₁` prime to `q₁`:
`d` is the normalized gcd. -/
theorem exists_monic_mul_eq_and_isCoprime {K : Type*} [Field K] {p q : K[X]}
    (hq : q ≠ 0) : ∃ d p₁ q₁, d.Monic ∧ d * p₁ = p ∧ d * q₁ = q ∧ IsCoprime p₁ q₁ := by
  classical
  obtain ⟨p₁, q₁, hp, hq₁, hu⟩ := extract_gcd p q
  exact ⟨gcd p q, p₁, q₁, normalize_gcd p q ▸ monic_normalize (gcd_ne_zero_of_right hq),
    hp.symm, hq₁.symm, (gcd_isUnit_iff _ _).mp hu⟩

end Polynomial
