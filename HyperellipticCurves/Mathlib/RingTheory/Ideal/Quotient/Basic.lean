/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The quotient by `1 - a`

## Main statements

* `Ideal.Quotient.mk_span_one_sub`: in `A ⧸ (1 - a)` the element `a` becomes `1`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- In `A ⧸ (1 - a)` the element `a` becomes `1`. -/
theorem Ideal.Quotient.mk_span_one_sub {A : Type*} [CommRing A] (a : A) :
    Ideal.Quotient.mk (Ideal.span {1 - a}) a = 1 :=
  (Ideal.Quotient.mk_eq_one_iff_sub_mem a).mpr (Ideal.mem_span_singleton.mpr ⟨-1, by ring⟩)

end
