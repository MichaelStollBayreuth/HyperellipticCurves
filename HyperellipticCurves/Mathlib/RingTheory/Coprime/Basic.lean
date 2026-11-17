/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling, for proofs only: the tactic `linear_combination`.
public import Mathlib.RingTheory.Coprime.Basic

import Mathlib.Tactic.LinearCombination

/-!
# Coprime elements: differences, products and congruences

## Main statements

* `Associated.isCoprime_iff_left`: coprimality is invariant under associates.
* `IsCoprime.sub_mul`: if `x` and `y` are coprime, so are `x - y` and `x * y`.
* `IsCoprime.exists_dvd_sub_and_dvd_sub`: the Chinese remainder theorem for two coprime
  elements.
* `isCoprime_iff_of_dvd_sub`: coprimality to `z` depends only on the residue modulo `z`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

theorem Associated.isCoprime_iff_left {R : Type*} [CommSemiring R] {x y z : R}
    (h : Associated x y) : IsCoprime x z ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := h
  hu ▸ (isCoprime_mul_unit_right_left u.isUnit x z).symm

variable {R : Type*} [CommRing R]

/-- If `u * x + v * y = 1`, then `x - y` is coprime to `x` and to `y`, hence to `x * y`. -/
theorem IsCoprime.sub_mul {x y : R} (h : IsCoprime x y) :
    IsCoprime (x - y) (x * y) := by
  obtain ⟨u, v, h⟩ := h
  exact .mul_right ⟨-v, u + v, by linear_combination h⟩ ⟨u, u + v, by linear_combination h⟩

/-- **Chinese remainder theorem** for two coprime elements; `Ideal.exists_forall_sub_mem_ideal`
is the version for a family of pairwise coprime ideals. -/
theorem IsCoprime.exists_dvd_sub_and_dvd_sub {m n : R} (h : IsCoprime m n) (s t : R) :
    ∃ k, m ∣ k - s ∧ n ∣ k - t := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨s * v * n + t * u * m, ⟨(t - s) * u, by linear_combination s * huv⟩,
    ⟨(s - t) * v, by linear_combination t * huv⟩⟩

theorem isCoprime_iff_of_dvd_sub {x y z : R} (h : z ∣ x - y) : IsCoprime x z ↔ IsCoprime y z := by
  obtain ⟨c, hc⟩ := h
  simp [sub_eq_iff_eq_add.mp hc]
