/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: `Polynomial.derivative` (statement) and `Polynomial.binomExpansion` (proof).
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Polynomial.Subring

import Mathlib.Algebra.Polynomial.Identities

/-!
# Polynomials with coefficients in a subring

## Main statements

* `Polynomial.exists_mem_eval_eq_add_mul`: Taylor expansion with a remainder in a subring: if the
  coefficients of `g` and the points `θ`, `x` lie in a subring `T`, then
  `g x = g θ + (x - θ) (g' θ + k (x - θ))` for some `k ∈ T`.

Auxiliary material for the valuations in the point lemma of the `x - T` descent; upstreaming
candidate for Mathlib.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **Taylor expansion with a remainder in a subring**: if the coefficients of `g` and the points
`θ`, `x` lie in a subring `T`, then `g x = g θ + (x - θ) (g' θ + k (x - θ))` for some `k ∈ T`. -/
theorem exists_mem_eval_eq_add_mul {T : Subring R} {g : R[X]} (hg : (g.coeffs : Set R) ⊆ T)
    {θ x : R} (hθ : θ ∈ T) (hx : x ∈ T) :
    ∃ k ∈ T, g.eval x = g.eval θ + (x - θ) * (g.derivative.eval θ + k * (x - θ)) := by
  obtain ⟨k, hk⟩ := binomExpansion (g.toSubring T hg) ⟨θ, hθ⟩ ⟨x - θ, T.sub_mem hx hθ⟩
  refine ⟨k, k.2, ?_⟩
  have h := congr(T.subtype $hk)
  simp only [map_add, map_mul, map_pow, ← eval_map_apply, ← derivative_map, map_toSubring,
    Subring.subtype_apply, add_sub_cancel] at h
  rw [h]
  ring

end Polynomial
