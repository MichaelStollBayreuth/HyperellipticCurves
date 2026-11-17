/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# The binomial coefficient `C(m + n, 2)`

## Main statements

* `Nat.add_choose_two`: `(m + n).choose 2 = m.choose 2 + n.choose 2 + m * n`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

theorem Nat.add_choose_two (m n : ℕ) : (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
  rw [Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ]
  ring
