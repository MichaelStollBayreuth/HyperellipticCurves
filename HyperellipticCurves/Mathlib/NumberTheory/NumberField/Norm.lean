/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.NumberField.Norm

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Algebraic integers of prime norm

## Main statements

* `NumberField.RingOfIntegers.prime_of_abs_norm_eq`: an algebraic integer whose norm is a prime
  number up to sign is a prime element.
* `NumberField.prime_of_abs_norm_eq`: an element of the integral closure of `ℤ` in `K`, for any
  `ℤ`-algebra structure on `K`, whose norm is a prime number up to sign is a prime element.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- An algebraic integer whose norm is a prime number up to sign is a prime element: the ideal it
generates has prime absolute norm. -/
theorem RingOfIntegers.prime_of_abs_norm_eq {x : 𝓞 K} {p : ℕ} (hp : p.Prime)
    (hx : |Algebra.norm ℚ (x : K)| = p) : Prime x := by
  have hN : (Algebra.norm ℤ x).natAbs = p := by
    rwa [← Nat.cast_inj (R := ℚ), Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
  exact Ideal.prime_of_irreducible_absNorm_span (by rwa [Ideal.absNorm_span_singleton, hN])

/-- `NumberField.RingOfIntegers.prime_of_abs_norm_eq` for the integral closure of `ℤ` in `K`, for
any `ℤ`-algebra structure on `K`: as `Algebra ℤ K` is a subsingleton, it is `𝓞 K`. The generality
is needed, as `AdjoinRoot g` carries a `ℤ`-algebra structure of its own, which is not reducibly
`Ring.toIntAlgebra`. -/
theorem prime_of_abs_norm_eq [Algebra ℤ K] {x : integralClosure ℤ K} {p : ℕ} (hp : p.Prime)
    (hx : |Algebra.norm ℚ (x : K)| = p) : Prime x := by
  obtain rfl := Subsingleton.elim ‹Algebra ℤ K› (Ring.toIntAlgebra K)
  exact RingOfIntegers.prime_of_abs_norm_eq (x := x) hp hx

end NumberField
