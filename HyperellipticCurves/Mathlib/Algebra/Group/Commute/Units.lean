/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Commute.Units

/-!
# Powers of units

## Main statements

* `exists_unit_eq_pow_iff`: a unit is an `n`-th power of a unit if and only if it is an `n`-th
  power of an element.

From Mathlib PR #44614 (`Units.ModPow`), which adds this lemma to the sibling file; delete it here
when the PR is merged.
-/

@[expose] public section

variable {M : Type*} [Monoid M] {n : ℕ}

/-- The unit `a` is an `n`-th power in `Mˣ` if and only if `a` is an `n`-th power in `M`. -/
@[to_additive /-- The additive unit `a` is an `n`-th multiple in `AddUnits M` if and only
if `a` is an `n`-th multiple in `M`. -/]
lemma exists_unit_eq_pow_iff {a : Mˣ} : (∃ x, a = x ^ n) ↔ ∃ (x : M), a = x ^ n := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, by simp [hx]⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  match n with
  | 0 => exact ⟨1, Units.ext <| by simp [hx]⟩
  | n + 1 => exact ⟨isUnit_pow_succ_iff.mp (hx ▸ a.isUnit) |>.unit, Units.ext <| by simp [← hx]⟩
