/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.Separable

-- Beyond the sibling, for the proof of `Algebra.IsSeparable.of_finrank_le_two` only: minimal
-- polynomials of elements of finite extensions, from `Mathlib.FieldTheory.Minpoly.Finite`.
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Separability of quadratic extensions, and simple roots of squarefree polynomials

## Main statements

* `Algebra.IsSeparable.of_finrank_le_two`: in characteristic `≠ 2`, every field extension of
  degree at most `2` is separable. Mathlib's generic criterion `Irreducible.separable` is
  restricted to characteristic `0`, and the derivative-degree API (`Polynomial.degree_derivative`
  etc.) requires torsion-free coefficients, so a direct coefficient computation is used.
* `Polynomial.eq_one_and_inj_of_squarefree_prod_X_sub_C_pow`: a squarefree product of powers of
  linear factors with nonzero exponents has all exponents `1` and pairwise distinct roots.
* `Polynomial.eval_derivative_ne_zero_of_squarefree`: a root of a squarefree polynomial over a
  field is a simple root.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial

/-- In characteristic ≠ 2, any field extension of degree at most 2 is separable:
the minimal polynomial of an element has degree 1 or 2, so its derivative has a
leading coefficient 1 or 2 and in particular does not vanish. -/
theorem Algebra.IsSeparable.of_finrank_le_two (F L : Type*) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (h2 : (2 : F) ≠ 0) (h : Module.finrank F L ≤ 2) :
    Algebra.IsSeparable F L := by
  refine ⟨fun x ↦ ?_⟩
  have hx : IsIntegral F x := .of_finite F x
  have hmon := minpoly.monic hx
  rw [IsSeparable, separable_iff_derivative_ne_zero (minpoly.irreducible hx)]
  have hd : (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = 2 := by
    lia [(minpoly.natDegree_le x).trans h, minpoly.natDegree_pos hx]
  intro hder
  rcases hd with hd | hd
  · have h0 := congrArg (fun q : F[X] ↦ q.coeff 0) hder
    have hc : (minpoly F x).coeff 1 = 1 := hd ▸ hmon.coeff_natDegree
    simp [coeff_derivative, hc] at h0
  · have h0 := congrArg (fun q : F[X] ↦ q.coeff 1) hder
    have hc : (minpoly F x).coeff 2 = 1 := hd ▸ hmon.coeff_natDegree
    simp only [coeff_derivative, coeff_zero, hc, one_mul, Nat.cast_one,
      one_add_one_eq_two] at h0
    exact h2 h0

namespace Polynomial

/-- If a product of powers of monic linear factors with nonzero exponents is squarefree, then
every exponent is `1` and the roots are pairwise distinct. -/
theorem eq_one_and_inj_of_squarefree_prod_X_sub_C_pow {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} {s : Finset ι} {x : ι → R} {k : ι → ℕ} (hk : ∀ i ∈ s, k i ≠ 0)
    (hsq : Squarefree (∏ i ∈ s, (X - C (x i)) ^ k i)) :
    (∀ i ∈ s, k i = 1) ∧ ∀ i ∈ s, ∀ j ∈ s, x i = x j → i = j := by
  classical
  have key {a : R} (h : (X - C a) * (X - C a) ∣ ∏ i ∈ s, (X - C (x i)) ^ k i) : False :=
    not_isUnit_X_sub_C _ (hsq _ h)
  have h1 i (hi : i ∈ s) : k i = 1 := by
    by_contra hne
    refine key (a := x i) ?_
    rw [← sq]
    exact (pow_dvd_pow _ ((Nat.two_le_iff _).mpr ⟨hk i hi, hne⟩)).trans
      (Finset.dvd_prod_of_mem _ hi)
  refine ⟨h1, fun i hi j hj hxij ↦ ?_⟩
  by_contra hne
  refine key (a := x i) ?_
  rw [← Finset.mul_prod_erase _ _ hi, h1 i hi, pow_one]
  refine mul_dvd_mul dvd_rfl ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨fun h ↦ hne h.symm, hj⟩),
    h1 j hj, pow_one, hxij]
  exact dvd_mul_right _ _

variable {K : Type*} [Field K]

/-- A root of a squarefree polynomial is a simple root. -/
theorem eval_derivative_ne_zero_of_squarefree {f : K[X]} (hsq : Squarefree f) {r : K}
    (hr : f.eval r = 0) : f.derivative.eval r ≠ 0 := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  intro h0
  have hd : f.derivative.eval r = q.eval r := by
    rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp
  rw [hd] at h0
  obtain ⟨p, hp⟩ := dvd_iff_isRoot.mpr h0
  exact not_isUnit_X_sub_C r (hsq (X - C r) ⟨p, by rw [hq, hp]; ring⟩)

end Polynomial

end
