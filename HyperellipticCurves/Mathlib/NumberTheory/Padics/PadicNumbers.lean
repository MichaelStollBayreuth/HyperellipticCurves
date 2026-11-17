/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Valuations of squares in `ℚ_[p]`

## Main statements

* `Padic.even_valuation_of_isSquare`, `Padic.norm_ne_norm_of_even_valuation_of_odd_valuation`: a
  square in `ℚ_[p]` has even valuation, and elements of even and of odd valuation have different
  norms.
* `Padic.norm_mul_sq_lt_one_of_odd_valuation`: if `‖α ^ 2 + D * β ^ 2‖ ≤ 1` for `D` of odd
  valuation, then `‖D * β ^ 2‖ < 1`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- A square in `ℚ_[p]` has even valuation. -/
theorem even_valuation_of_isSquare {x : ℚ_[p]} (hx : IsSquare x) : Even x.valuation := by
  obtain ⟨y, rfl⟩ := hx
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · exact ⟨_, valuation_mul hy hy⟩

theorem ne_zero_of_odd_valuation {x : ℚ_[p]} (hx : Odd x.valuation) : x ≠ 0 := by
  rintro rfl
  simp at hx

/-- Elements of `ℚ_[p]` of even and of odd valuation have different norms. -/
theorem norm_ne_norm_of_even_valuation_of_odd_valuation {x y : ℚ_[p]} (hx : Even x.valuation)
    (hy : Odd y.valuation) : ‖x‖ ≠ ‖y‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa [eq_comm] using ne_zero_of_odd_valuation hy
  rw [norm_eq_zpow_neg_valuation hx0, norm_eq_zpow_neg_valuation (ne_zero_of_odd_valuation hy)]
  intro h
  have := zpow_right_injective₀ (mod_cast (Fact.out : p.Prime).pos)
    (mod_cast (Fact.out : p.Prime).ne_one) h
  exact Int.not_even_iff_odd.mpr hy (neg_injective this ▸ hx)

/-- If `‖α ^ 2 + D * β ^ 2‖ ≤ 1` for `D` of odd valuation, then `‖D * β ^ 2‖ < 1`: the valuations
of `α ^ 2` and of `D * β ^ 2` have different parities. -/
theorem norm_mul_sq_lt_one_of_odd_valuation {D α β : ℚ_[p]} (hD : Odd D.valuation)
    (h : ‖α ^ 2 + D * β ^ 2‖ ≤ 1) : ‖D * β ^ 2‖ < 1 := by
  rcases eq_or_ne β 0 with rfl | hβ
  · simp
  have hodd : Odd (D * β ^ 2).valuation := by
    rw [valuation_mul (ne_zero_of_odd_valuation hD) (pow_ne_zero 2 hβ)]
    exact hD.add_even (even_valuation_of_isSquare (.sq β))
  have h1 : ‖D * β ^ 2‖ ≠ 1 := by
    simpa using (norm_ne_norm_of_even_valuation_of_odd_valuation (x := 1) (by simp) hodd).symm
  rw [add_eq_max_of_ne (norm_ne_norm_of_even_valuation_of_odd_valuation
    (even_valuation_of_isSquare (.sq α)) hodd)] at h
  exact ((le_max_right _ _).trans h).lt_of_ne h1

end Padic
