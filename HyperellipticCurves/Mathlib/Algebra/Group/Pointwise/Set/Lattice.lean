/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.Algebra.Group.Pointwise.Set.Lattice`: `Set.Finite`, for the
-- statement of `Set.Finite.mul_iInter_of_directed`, and `Directed.finite_le`, for its proof.
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Basic.Finite.Defs

import Mathlib.Data.Fintype.Order

/-!
# The product of a finite set and an intersection of sets

Mathlib has the inclusion `Set.mul_iInter_subset : s * ⋂ i, t i ⊆ ⋂ i, s * t i` for sets in a
type with a multiplication. If the multiplication is left-cancellative, for instance in a group, it
is an equality when `s` is finite and the family `t` is directed downward.

## Main statements

* `Set.Finite.mul_iInter_of_directed`: `s * ⋂ i, t i = ⋂ i, s * t i` for a finite set `s` and a
  family `t` that is directed downward, for a left-cancellative multiplication.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

open scoped Pointwise

namespace Set

variable {α : Type*} [Mul α] [IsLeftCancelMul α]

/-- The inclusion `Set.mul_iInter_subset` is an equality for a finite set `s` and a family `t`
that is directed downward: if `a` lies in every `s * t i` but not in `s * ⋂ i, t i`, then, by left
cancellation, each `x ∈ s` has an index `i x` with `x * b ≠ a` for every `b ∈ t (i x)`, and an
index below all of them contradicts the choice. -/
@[to_additive /-- The inclusion `Set.add_iInter_subset` is an equality for a finite set `s` and a
family `t` that is directed downward: if `a` lies in every `s + t i` but not in `s + ⋂ i, t i`,
then, by left cancellation, each `x ∈ s` has an index `i x` with `x + b ≠ a` for every
`b ∈ t (i x)`, and an index below all of them contradicts the choice. -/]
theorem Finite.mul_iInter_of_directed {ι : Sort*} [Nonempty ι] {s : Set α} (hs : s.Finite)
    {t : ι → Set α} (ht : Directed (· ⊇ ·) t) :
    s * ⋂ i, t i = ⋂ i, s * t i := by
  refine (mul_iInter_subset s t).antisymm fun a ha ↦ ?_
  by_contra h
  have (x : s) : ∃ i, ∀ b ∈ t i, x * b ≠ a := by
    by_contra! H
    obtain ⟨b, -, rfl⟩ := H (Classical.arbitrary ι)
    refine h ⟨x, x.2, b, mem_iInter.mpr fun i ↦ ?_, rfl⟩
    obtain ⟨c, hc, hcb⟩ := H i
    exact mul_left_cancel hcb ▸ hc
  choose i hi using this
  have := hs.to_subtype
  obtain ⟨k, hk⟩ := ht.finite_le i
  obtain ⟨x, hx, b, hb, rfl⟩ := mem_iInter.mp ha k
  exact hi ⟨x, hx⟩ b (hk ⟨x, hx⟩ hb) rfl

end Set
