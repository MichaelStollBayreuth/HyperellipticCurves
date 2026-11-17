/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# The order of finite products of Hahn series

## Main statements

* `HahnSeries.sum_le_orderTop_prod`: a finite product of Hahn series bounded below in order is
  bounded below by the sum of the bounds.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace HahnSeries

variable {Γ R ι : Type*}

/-- A product of Hahn series bounded below in order is bounded below by the sum of the
bounds. -/
theorem sum_le_orderTop_prod [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [CommSemiring R] [Nontrivial R] {s : Finset ι} {f : ι → HahnSeries Γ R} {a : ι → Γ}
    (h : ∀ i ∈ s, (a i : WithTop Γ) ≤ (f i).orderTop) :
    ((∑ i ∈ s, a i : Γ) : WithTop Γ) ≤ (∏ i ∈ s, f i).orderTop := by
  induction s using Finset.cons_induction with
  | empty => simp [orderTop_one]
  | cons i s hi ih =>
    rw [Finset.sum_cons, Finset.prod_cons]
    refine le_trans ?_ orderTop_add_le_mul
    rw [WithTop.coe_add]
    exact add_le_add (h i (Finset.mem_cons_self ..)) (ih fun j hj ↦ h j
      (Finset.mem_cons_of_mem hj))

end HahnSeries

end
