/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.HahnSeries.Addition

/-!
# The order of finite sums of Hahn series

## Main statements

* `HahnSeries.le_orderTop_sum`, `HahnSeries.lt_orderTop_sum`: termwise lower bounds on
  `HahnSeries.orderTop` transfer to finite sums.
* `HahnSeries.orderTop_add_sum_eq`: **the dominated-sum principle** — an element of exact order
  `V` plus a sum of terms of order above `V` has exact order `V`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace HahnSeries

variable {Γ R ι : Type*}

/-- A sum of Hahn series bounded below in order is bounded below in order. -/
theorem le_orderTop_sum [LinearOrder Γ] [AddCommMonoid R] {s : Finset ι}
    {f : ι → HahnSeries Γ R} {a : WithTop Γ} (h : ∀ i ∈ s, a ≤ (f i).orderTop) :
    a ≤ (∑ i ∈ s, f i).orderTop := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    exact le_trans (le_min (h i (Finset.mem_cons_self ..))
      (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))) min_orderTop_le_orderTop_add

/-- A sum of Hahn series of order above a threshold has order above the threshold. -/
theorem lt_orderTop_sum [LinearOrder Γ] [AddCommMonoid R] {s : Finset ι}
    {f : ι → HahnSeries Γ R} {a : Γ} (h : ∀ i ∈ s, (a : WithTop Γ) < (f i).orderTop) :
    (a : WithTop Γ) < (∑ i ∈ s, f i).orderTop := by
  induction s using Finset.cons_induction with
  | empty => simp [WithTop.coe_lt_top]
  | cons i s hi ih =>
    rw [Finset.sum_cons]
    exact lt_of_lt_of_le (lt_min (h i (Finset.mem_cons_self ..))
      (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))) min_orderTop_le_orderTop_add

/-- **The dominated-sum principle**: an element of exact order `V` plus a sum of terms of
order above `V` has exact order `V`. -/
theorem orderTop_add_sum_eq [LinearOrder Γ] [AddCommMonoid R] {s : Finset ι}
    {x : HahnSeries Γ R} {f : ι → HahnSeries Γ R} {V : Γ}
    (hx : x.orderTop = (V : WithTop Γ)) (hf : ∀ i ∈ s, (V : WithTop Γ) < (f i).orderTop) :
    (x + ∑ i ∈ s, f i).orderTop = (V : WithTop Γ) := by
  rw [orderTop_add_eq_left (by rw [hx]; exact lt_orderTop_sum hf), hx]

end HahnSeries

end
