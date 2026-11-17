/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient

import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Basic

/-!
# Degree bounds for division by a monic polynomial

## Main statements

* `Polynomial.modByMonic_mem_degreeLT`: for monic `g`, the remainder `q %ₘ g` lies in
  `R[X]_(deg g)`.
* `Polynomial.divByMonic_mem_degreeLT`: for monic `g` and `q ∈ R[X]_(deg g + n)`, the quotient
  `q /ₘ g` lies in `R[X]_n`.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`), for the norm of
`AdjoinRoot.mk g p` as a resultant; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Ring R] [Nontrivial R] {g q : R[X]} {n : ℕ}

theorem modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) : q %ₘ g ∈ degreeLT R g.natDegree :=
  (mem_degreeLT_natDegree_iff hg.ne_zero).mpr <| degree_modByMonic_lt q hg

theorem divByMonic_mem_degreeLT (hg : g.Monic) (hq : q ∈ degreeLT R (g.natDegree + n)) :
    q /ₘ g ∈ degreeLT R n := by
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

end Polynomial
