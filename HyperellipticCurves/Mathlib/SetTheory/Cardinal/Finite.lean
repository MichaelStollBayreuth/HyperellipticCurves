/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting subsets in complementary pairs

## Main statements

* `Finset.natCard_subtype_eq_two_pow_of_compl_iff_not`: a property that holds for exactly one of
  each pair of complementary subsets of a finite type holds for `2 ^ (card α - 1)` of them.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Finset

/-- A property of the subsets of a finite type that holds for exactly one of each pair of
complementary subsets holds for half of them. The hypothesis forces `α` to be nonempty. -/
theorem natCard_subtype_eq_two_pow_of_compl_iff_not {α : Type*} [Fintype α] [DecidableEq α]
    {P : Finset α → Prop} (h : ∀ s, P sᶜ ↔ ¬P s) :
    Nat.card {s : Finset α // P s} = 2 ^ (Fintype.card α - 1) := by
  classical
  have e : {s : Finset α // ¬P s} ≃ {s // P s} :=
    (compl_involutive.toPerm _).subtypeEquiv fun s ↦ (h s).symm
  have h₂ : Nat.card {s // P s} + Nat.card {s // P s} = 2 ^ Fintype.card α := by
    nth_rw 2 [← Nat.card_congr e]
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl P), Nat.card_eq_fintype_card,
      Fintype.card_finset]
  generalize Fintype.card α = n at h₂ ⊢
  cases n with
  | zero => lia [pow_zero 2]
  | succ n => lia [pow_succ 2 n]

end Finset
