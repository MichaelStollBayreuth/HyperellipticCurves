/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ENat.Basic

-- Beyond the sibling, for the proof only: the canonically ordered additive monoid `ℕ∞`
-- (`le_self_add`, `le_add_self`), from `Mathlib.Data.ENat.Monoid`.
import Mathlib.Data.ENat.Monoid

/-!
# Natural-number values of a sum in `ℕ∞`

## Main statements

* `ENat.toNat_add_toNat_of_add_eq_natCast`: from `a + b = ↑n` in `ℕ∞` one recovers
  `a.toNat + b.toNat = n` in `ℕ`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace ENat

/-- Extracting the two `ℕ`-values from an `ℕ∞`-identity `a + b = ↑n`. -/
theorem toNat_add_toNat_of_add_eq_natCast {a b : ℕ∞} {n : ℕ} (h : a + b = ↑n) :
    a.toNat + b.toNat = n := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (natCast_ne_top n) (h ▸ le_self_add)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top (natCast_ne_top n) (h ▸ le_add_self)
  rw [← toNat_add ha hb, h, toNat_natCast]

end ENat

end
