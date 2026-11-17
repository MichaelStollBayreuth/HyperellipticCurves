/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Invertibility of `2` in quotient rings

## Main statements

* `Ideal.Quotient.invertibleTwo`: an `Invertible (2 : R)` descends to `R ⧸ I`.

The general numeral `OfNat.ofNat n` version does not fire in instance search, hence the
numeral `2`, as for Mathlib's `invertibleTwo`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- Invertibility of `2` descends to quotient rings. -/
instance Ideal.Quotient.invertibleTwo {R : Type*} [CommRing R] (I : Ideal R) [Invertible (2 : R)] :
    Invertible (2 : R ⧸ I) :=
  (Invertible.map (Ideal.Quotient.mk I) 2).copy _ (map_ofNat _ 2).symm

end
