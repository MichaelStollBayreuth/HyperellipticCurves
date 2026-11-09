/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Disks.CanonDeg

import HyperellipticCurves.Archive.ForMathlib.Polynomial
import HyperellipticCurves.ForMathlib.Polynomial

/-!
# The exact canonical degree

Over an algebraically closed field the degree of `div(h̄ dx/y)` is *exactly* `2g-2`
(`deg_div_omega_bar`, blueprint `lem:canon-deg`, via the exact fibre count `fiber_sum`). The
main theorems do not depend on it: the count consumes only the one-sided budget `cor:sum-ord`
(`ChabautyColeman.sum_ord_le`), proved directly over any field; the exact degree serves as a
consistency check of the `ordPoint` bookkeeping.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {κ : Type*} [Field κ] {f : κ[X]}
  [NeZero (2 : κ)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]

variable [IsAlgClosed κ]

/-- The total order over the fiber `{(x₀, y₀) : y₀² = f(x₀)}` above `x₀` is `2·rootMultiplicity`
(over an algebraically closed field a square root of `f(x₀)` always exists). -/
theorem fiber_sum {x₀ : κ} {h : κ[X]} (hh : h ≠ 0) :
    ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x₀},
        (emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat
      = 2 * rootMultiplicity x₀ h :=
  have ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (f.eval x₀) (n := 2) (by norm_num)
  fiber_sum_of_sq hb hh

/-- **Canonical degree (`lem:canon-deg`).** For `0 ≠ h` of degree `≤ g-1`, the degree of
`div(h̄ dx/y)` on the residue curve — the affine point-sum plus the order `2g-2-2·deg h` at `∞` —
is `2g-2`. The affine part is `∑_{x₀} (fiber = 2·rootMult) = 2·deg h`. -/
theorem deg_div_omega_bar {h : κ[X]} (hh : h ≠ 0) (hdeg : h.natDegree ≤ genus f - 1)
    (hg : 1 ≤ genus f) :
    (∑ᶠ x₀ : κ, ∑ᶠ y₀ ∈ {y : κ | y ^ 2 = f.eval x₀},
        (emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap κ[X] (HypRing κ f) h})).toNat)
        + (2 * (genus f - 1) - 2 * h.natDegree)
      = 2 * genus f - 2 := by
  classical
  have hfin : (Function.support (fun x₀ : κ ↦ rootMultiplicity x₀ h)).Finite :=
    h.roots.toFinset.finite_toSet.subset (support_rootMultiplicity_subset h)
  rw [finsum_congr fun x₀ ↦ fiber_sum hh, ← mul_finsum' _ 2 hfin, finsum_rootMultiplicity]
  lia

end ChabautyColeman

end
