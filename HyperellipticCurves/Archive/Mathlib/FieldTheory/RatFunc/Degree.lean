/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Degree bounds for rational functions

The predicate `RatFunc.IntDegreeLE x c` ("`x` is zero or has `intDegree ≤ c`") and its closure
properties, for pole-order bookkeeping at infinity.

## Main definitions

* `RatFunc.IntDegreeLE`: `x = 0 ∨ x.intDegree ≤ c`; the junk value `intDegree 0 = 0` makes the
  raw inequality useless for bounds `c < 0`.

## Main statements

* `RatFunc.IntDegreeLE.add`, `RatFunc.IntDegreeLE.neg`, `RatFunc.IntDegreeLE.mul`,
  `RatFunc.IntDegreeLE.sum`: closure under the ring operations and finite sums.
* `RatFunc.intDegree_sub_eq_max`: the degree of a difference of rational functions of distinct
  degrees is the larger degree.
* `RatFunc.exists_sub_C_intDegreeLE`: a rational function of nonpositive degree is a constant
  plus a part of negative degree.

Its clients are the second-kind classification (`HyperellipticCurves.Archive.SecondKind`), the
place-by-place valuation bounds (`HyperellipticCurves.Archive.OmegaRegular`), the transport of
the function field to the infinite place (`HyperellipticCurves.Archive.InftyTransport`) and the
derivative of a rational function (`HyperellipticCurves.Archive.RatFuncDerivative`), all in the
Archive. The trace-form route of the main development exhibits the regular numerator outright
and never bounds a degree.

Auxiliary material for the Archive of the formalization of the Chabauty–Coleman bound for
hyperelliptic curves (the main theorems do not depend on it); upstreaming candidates for
Mathlib.
-/

@[expose] public section

open Polynomial

namespace RatFunc

variable {K : Type*} [Field K]

/-- Degree bound predicate for rational functions: `x` is zero or has `intDegree ≤ c`.
The junk value `intDegree 0 = 0` makes the raw inequality useless for bounds `c < 0`;
this disjunction is the composable currency for pole-order bookkeeping at infinity. -/
def IntDegreeLE (x : RatFunc K) (c : ℤ) : Prop := x = 0 ∨ x.intDegree ≤ c

theorem intDegreeLE_zero (c : ℤ) : (0 : RatFunc K).IntDegreeLE c := .inl rfl

theorem IntDegreeLE.of_le {x : RatFunc K} {c d : ℤ} (h : x.IntDegreeLE c) (hcd : c ≤ d) :
    x.IntDegreeLE d :=
  h.imp id fun h' ↦ h'.trans hcd

theorem intDegreeLE_algebraMap (p : K[X]) :
    (algebraMap K[X] (RatFunc K) p).IntDegreeLE p.natDegree :=
  .inr (by rw [intDegree_polynomial])

theorem IntDegreeLE.add {x y : RatFunc K} {c : ℤ} (hx : x.IntDegreeLE c)
    (hy : y.IntDegreeLE c) : (x + y).IntDegreeLE c := by
  rcases eq_or_ne (x + y) 0 with h0 | h0
  · exact .inl h0
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using hy
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using hx
  exact .inr ((intDegree_add_le h0).trans
    (max_le (hx.resolve_left hx0) (hy.resolve_left hy0)))

theorem IntDegreeLE.neg {x : RatFunc K} {c : ℤ} (hx : x.IntDegreeLE c) :
    (-x).IntDegreeLE c := by
  rcases hx with rfl | hx
  · rw [neg_zero]; exact intDegreeLE_zero c
  · exact .inr (by rwa [intDegree_neg])

theorem IntDegreeLE.mul {x y : RatFunc K} {c d : ℤ} (hx : x.IntDegreeLE c)
    (hy : y.IntDegreeLE d) : (x * y).IntDegreeLE (c + d) := by
  rcases hx with rfl | hx
  · rw [zero_mul]; exact intDegreeLE_zero _
  rcases hy with rfl | hy
  · rw [mul_zero]; exact intDegreeLE_zero _
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_mul]; exact intDegreeLE_zero _
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]; exact intDegreeLE_zero _
  exact .inr ((intDegree_mul hx0 hy0).le.trans (add_le_add hx hy))

theorem IntDegreeLE.sum {ι : Type*} {s : Finset ι} {g : ι → RatFunc K} {c : ℤ}
    (h : ∀ i ∈ s, (g i).IntDegreeLE c) : (∑ i ∈ s, g i).IntDegreeLE c := by
  classical
  induction s using Finset.induction with
  | empty => simpa using intDegreeLE_zero c
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- The `intDegree` of a difference of rational functions of distinct degrees is the
maximum of the degrees (the ultrametric equality case). -/
theorem intDegree_sub_eq_max {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : x.intDegree ≠ y.intDegree) :
    (x - y).intDegree = max x.intDegree y.intDegree := by
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (by rw [h])
  have hle : (x - y).intDegree ≤ max x.intDegree y.intDegree := by
    rw [sub_eq_add_neg]
    exact (intDegree_add_le (by rwa [← sub_eq_add_neg])).trans
      (by rw [intDegree_neg])
  rcases lt_or_gt_of_ne hne with h | h
  · have hmax : max x.intDegree y.intDegree = y.intDegree := max_eq_right h.le
    have h2 := intDegree_add_le (y := -(x - y))
      (show x + -(x - y) ≠ 0 by intro h0; exact hy (by linear_combination h0))
    rw [show x + -(x - y) = y by ring, intDegree_neg] at h2
    rw [hmax] at hle ⊢
    rcases max_cases x.intDegree (x - y).intDegree with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at h2 <;> lia
  · have hmax : max x.intDegree y.intDegree = x.intDegree := max_eq_left h.le
    have h2 := intDegree_add_le (y := x - y)
      (show y + (x - y) ≠ 0 by intro h0; exact hx (by linear_combination h0))
    rw [show y + (x - y) = x by ring] at h2
    rw [hmax] at hle ⊢
    rcases max_cases y.intDegree (x - y).intDegree with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at h2 <;> lia

/-- A rational function of nonpositive degree is a constant plus a strictly negative-degree
part (split off the monic-division constant `num /ₘ denom`). -/
theorem exists_sub_C_intDegreeLE {x : RatFunc K} (hx : x.IntDegreeLE 0) :
    ∃ c : K, (x - RatFunc.C c).IntDegreeLE (-1) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simpa using intDegreeLE_zero (-1)⟩
  have hdeg : x.num.natDegree ≤ x.denom.natDegree := by
    lia [hx.resolve_left hx0,
      (show x.intDegree = (x.num.natDegree : ℤ) - x.denom.natDegree from rfl)]
  have hquot : (x.num /ₘ x.denom).natDegree = 0 := by
    rw [Polynomial.natDegree_divByMonic _ (monic_denom x)]
    lia
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hquot
  refine ⟨c, ?_⟩
  have hden : algebraMap K[X] (RatFunc K) x.denom ≠ 0 := algebraMap_ne_zero x.denom_ne_zero
  have hpoly : x.num = x.denom * Polynomial.C c + x.num %ₘ x.denom := by
    rw [hc]
    linear_combination (Polynomial.modByMonic_add_div x.num x.denom).symm
  have hx' : x * algebraMap K[X] (RatFunc K) x.denom
      = algebraMap K[X] (RatFunc K) x.num := ((div_eq_iff hden).mp (num_div_denom x)).symm
  have hxc : x - RatFunc.C c
      = algebraMap K[X] (RatFunc K) (x.num %ₘ x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [eq_div_iff hden, sub_mul, hx', ← algebraMap_C, ← map_mul, ← map_sub]
    congr 1
    linear_combination hpoly
  rcases eq_or_ne (x.num %ₘ x.denom) 0 with h0 | h0
  · rw [hxc, h0, map_zero, zero_div]
    exact intDegreeLE_zero _
  refine .inr ?_
  rw [hxc, intDegree_div (algebraMap_ne_zero h0) hden, intDegree_polynomial,
    intDegree_polynomial]
  have hlt : (x.num %ₘ x.denom).natDegree < x.denom.natDegree := by
    have h := Polynomial.degree_modByMonic_lt x.num (monic_denom x)
    exact Polynomial.natDegree_lt_natDegree h0 h
  lia

end RatFunc

end
