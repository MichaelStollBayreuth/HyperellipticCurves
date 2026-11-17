/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Localization.Defs

/-!
# Invertibility of `2` in localizations

## Main statements

* `Localization.invertibleTwo`: an `Invertible (2 : R)` ascends to `Localization M`, in
  particular to the fraction ring.

The general numeral `OfNat.ofNat n` version does not fire in instance search, hence the
numeral `2`, as for Mathlib's `invertibleTwo`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- Invertibility of `2` ascends to localizations, in particular to the fraction ring. -/
instance Localization.invertibleTwo {R : Type*} [CommRing R] (M : Submonoid R)
    [Invertible (2 : R)] : Invertible (2 : Localization M) :=
  (Invertible.map (algebraMap R (Localization M)) 2).copy _ (map_ofNat _ 2).symm

end
