/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# The Leibniz rule in multiplicative form

## Main statements

* `Derivation.leibniz_mul`: `d (p * q) = d p * q + p * d q` for a derivation of a commutative
  ring into itself (`Derivation.leibniz` states it with a scalar action).

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- The Leibniz rule for a derivation of a commutative ring into itself, in `mul` form. -/
theorem Derivation.leibniz_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (d : Derivation R A A) (p q : A) : d (p * q) = d p * q + p * d q := by
  rw [d.leibniz, smul_eq_mul, smul_eq_mul]; ring

end
