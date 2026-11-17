/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# `ℤˣ` as `ℤ / 2`

## Main definitions

* `Int.unitsMulEquivZModTwo`: the group `ℤˣ = {±1}` as `Multiplicative (ZMod 2)`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

/-- The group `ℤˣ = {±1}` as `ℤ / 2`, written multiplicatively: `1 ↦ 0`, `-1 ↦ 1`. -/
def Int.unitsMulEquivZModTwo : ℤˣ ≃* Multiplicative (ZMod 2) where
  toFun u := .ofAdd (if u = 1 then 0 else 1)
  invFun z := if z = 1 then 1 else -1
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide
