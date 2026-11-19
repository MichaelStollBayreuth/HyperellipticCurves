/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefreeness along multiplicative equivalences, and divisors of `b ^ 2 - f`

## Main statements

* `MulEquiv.squarefree_iff`: an element is squarefree if and only if its image under a
  multiplicative equivalence is, with `Squarefree.map` the direction used in practice.
* `Squarefree.isUnit_of_isSquare`: a squarefree square is a unit.
* `Squarefree.dvd_of_dvd_of_dvd_sq_sub`: `d ∣ f` and `d ∣ b ^ 2 - f` give `d ∣ b`.
* `Squarefree.isRelPrime_of_dvd_of_mul_dvd_sq_sub`: `d ∣ f` and `d * e ∣ b ^ 2 - f` give
  `IsRelPrime d e`.

The last two are for a squarefree `f` and a divisor `d` of `f` (for polynomials: the common part of
`f` and the first polynomial of a Mumford pair `(a, b)`).

Auxiliary material for the formalization of the Chabauty–Coleman bound and of `2`-descent for
hyperelliptic curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Squarefreeness is invariant under multiplicative equivalences. -/
theorem MulEquiv.squarefree_iff {M N F : Type*} [Monoid M] [Monoid N] [EquivLike F M N]
    [MulEquivClass F M N] (f : F) {x : M} : Squarefree (f x) ↔ Squarefree x := by
  simp [Squarefree, (EquivLike.surjective f).forall, ← map_mul, map_dvd_iff, -isUnit_map_iff]

alias ⟨_, Squarefree.map⟩ := MulEquiv.squarefree_iff

/-- `x = r * r` makes `r`, and with it `x`, a unit. -/
theorem Squarefree.isUnit_of_isSquare {R : Type*} [Monoid R] {x : R} (hx : Squarefree x)
    (h : IsSquare x) : IsUnit x := by
  obtain ⟨r, rfl⟩ := h
  exact (hx r dvd_rfl).mul (hx r dvd_rfl)

variable {R : Type*} [CommRing R] [DecompositionMonoid R] {f d b : R}

/-- A divisor `d` of `f` and `b ^ 2 - f` divides `b ^ 2`, and it is squarefree as a divisor of the
squarefree `f`, so it divides `b`. -/
theorem Squarefree.dvd_of_dvd_of_dvd_sq_sub (hf : Squarefree f) (hd : d ∣ f)
    (h : d ∣ b ^ 2 - f) : d ∣ b :=
  ((hf.squarefree_of_dvd hd).dvd_pow_iff_dvd two_ne_zero).mp ((dvd_sub_left hd).mp h)

/-- A common divisor `t` of `d` and `e` divides `b` by `Squarefree.dvd_of_dvd_of_dvd_sq_sub`, so
`t * t` divides `b ^ 2` and `b ^ 2 - f`, hence the squarefree `f`. -/
theorem Squarefree.isRelPrime_of_dvd_of_mul_dvd_sq_sub {e : R} (hf : Squarefree f) (hd : d ∣ f)
    (h : d * e ∣ b ^ 2 - f) : IsRelPrime d e := fun t htd hte ↦ by
  have hb := hf.dvd_of_dvd_of_dvd_sq_sub (htd.trans hd) ((htd.trans (dvd_mul_right d e)).trans h)
  exact hf t ((dvd_sub_right (sq b ▸ mul_dvd_mul hb hb)).mp ((mul_dvd_mul htd hte).trans h))

end
