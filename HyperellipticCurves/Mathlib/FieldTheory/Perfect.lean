/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Perfect

/-!
# Squarefree polynomials over a perfect field

## Main statements

* `Squarefree.map_of_perfectField`: over a perfect field, the image of a squarefree polynomial
  under a ring homomorphism is squarefree.

Auxiliary material for the base change of the `x - T` descent to completions; upstreaming
candidate for Mathlib.
-/

@[expose] public section

open Polynomial

/-- Over a perfect field, the image of a squarefree polynomial under any ring homomorphism is
squarefree: it is separable (`PerfectField.separable_iff_squarefree`), and separability is
preserved by `Polynomial.map`. -/
theorem Squarefree.map_of_perfectField {K L : Type*} [Field K] [PerfectField K] [CommSemiring L]
    {f : K[X]} (hf : Squarefree f) (φ : K →+* L) : Squarefree (f.map φ) :=
  (PerfectField.separable_iff_squarefree.mpr hf).map.squarefree
