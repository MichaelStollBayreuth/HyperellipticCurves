/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products over a symmetric difference

## Main statements

* `Finset.prod_symmDiff_of_sq_eq_one`: the product over `s ∆ t` of a function whose values on
  `s ∩ t` square to `1` is the product of the products over `s` and over `t`.
* `Finset.prod_injective_of_sq_eq_one`: for elements whose squares are `1` and whose only
  trivial product is the empty one, the products over distinct finite sets are distinct.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Finset

open scoped symmDiff

variable {ι : Type*}

section CommMonoid

variable {M : Type*} [CommMonoid M] [DecidableEq ι] {s t : Finset ι} {f : ι → M}

/-- Over the symmetric difference, the product of a function whose values on `s ∩ t` square to `1`
is the product of the products over `s` and over `t`: the factors over `s ∩ t` occur twice. -/
theorem prod_symmDiff_of_sq_eq_one (hf : ∀ i ∈ s ∩ t, f i ^ 2 = 1) :
    ∏ i ∈ s ∆ t, f i = (∏ i ∈ s, f i) * ∏ i ∈ t, f i := by
  rw [← prod_union_inter, ← sup_eq_union, ← symmDiff_sup_inf, sup_eq_union,
    prod_union (disjoint_symmDiff_inf s t), inf_eq_inter, mul_assoc, ← sq, ← prod_pow,
    prod_eq_one hf, mul_one]

end CommMonoid

variable {G : Type*} [CommGroup G] {g : ι → G}

/-- For elements whose squares are `1`, the products over distinct finite sets of indices are
distinct as soon as the empty set is the only one with product `1`: the product over the symmetric
difference of two sets is the product of their products
(`Finset.prod_symmDiff_of_sq_eq_one`). -/
theorem prod_injective_of_sq_eq_one (hg : ∀ i, g i ^ 2 = 1)
    (h : ∀ s : Finset ι, ∏ i ∈ s, g i = 1 → s = ∅) :
    Function.Injective fun s : Finset ι ↦ ∏ i ∈ s, g i := by
  classical
  refine fun s t (hst : ∏ i ∈ s, g i = ∏ i ∈ t, g i) ↦ symmDiff_eq_bot.mp <| h _ ?_
  rw [prod_symmDiff_of_sq_eq_one fun i _ ↦ hg i, hst, ← sq, ← prod_pow, prod_eq_one fun i _ ↦ hg i]

end Finset
