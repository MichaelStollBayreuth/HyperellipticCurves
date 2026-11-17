/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: the product with a matrix (`Matrix.vecMul`) in the statement of
-- `Polynomial.exists_ne_zero_forall_mem_degreeLT_and_dvd_vecMul`, and for its proof the linear
-- algebra over the quotients `AdjoinRoot (m j)`.
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Polynomial.Basic

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot

/-!
# Polynomials of bounded degree

## Main statements

* `Polynomial.mem_degreeLT_of_natDegree_lt`, `Polynomial.mem_degreeLT_natDegree_add_one`,
  `Polynomial.mul_mem_degreeLT`: membership in `Polynomial.degreeLT` from the natural degree, and
  for products.
* `Polynomial.mem_degreeLT_natDegree_iff`: membership in `R[X]_(deg g)` from the degree.
* `Polynomial.exists_ne_zero_forall_mem_degreeLT_and_dvd_vecMul`: a system of homogeneous linear
  congruences modulo nonzero polynomials with more unknown coefficients than conditions has a
  nonzero solution of bounded degrees.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial Module
open scoped Matrix

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R]

theorem mem_degreeLT_of_natDegree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    p ∈ degreeLT R n :=
  mem_degreeLT.mpr <| degree_le_natDegree.trans_lt <| mod_cast h

theorem mem_degreeLT_natDegree_add_one (p : R[X]) : p ∈ degreeLT R (p.natDegree + 1) :=
  mem_degreeLT_of_natDegree_lt p.natDegree.lt_add_one

/-- The product of polynomials of degrees `< m` and `< n` has degree `< m + n - 1`; for `m = 0`
or `n = 0` one factor is `0`. -/
theorem mul_mem_degreeLT {p q : R[X]} {m n : ℕ} (hp : p ∈ degreeLT R m)
    (hq : q ∈ degreeLT R n) : p * q ∈ degreeLT R (m + n - 1) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt hp0] at hp
  rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt hq0] at hq
  exact mem_degreeLT_of_natDegree_lt <| natDegree_mul_le.trans_lt (by lia)

theorem mem_degreeLT_natDegree_iff {g q : R[X]} (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]

end Semiring

/-- A system of homogeneous linear congruences `x ᵥ* B ≡ 0` modulo nonzero polynomials `m j`
over a field has a nonzero solution with `deg x i < n i` once the number `∑ i, n i` of unknown
coefficients exceeds the number `∑ j, deg (m j)` of conditions: the solutions are the kernel of a
linear map from `∏ i, K[X]_{n i}` to `∏ j, K[X] ⧸ (m j)`. -/
theorem exists_ne_zero_forall_mem_degreeLT_and_dvd_vecMul {K : Type*} [Field K] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (m : κ → K[X]) (hm : ∀ j, m j ≠ 0) (B : Matrix ι κ K[X])
    (n : ι → ℕ) (h : ∑ j, (m j).natDegree < ∑ i, n i) :
    ∃ x ≠ 0, (∀ i, x i ∈ degreeLT K (n i)) ∧ ∀ j, m j ∣ (x ᵥ* B) j := by
  have (j : κ) : Module.Finite K (AdjoinRoot (m j)) := (AdjoinRoot.powerBasis (hm j)).finite
  have (i : ι) : Module.Finite K (degreeLT K (n i)) := .equiv (degreeLTEquiv K (n i)).symm
  let φ := (LinearMap.piMap fun j ↦ (AdjoinRoot.mkₐ (m j)).toLinearMap) ∘ₗ
    (B.vecMulLinear.restrictScalars K) ∘ₗ LinearMap.piMap fun i ↦ (degreeLT K (n i)).subtype
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp <| φ.ker_ne_bot_of_finrank_lt <| by
    simp_rw [finrank_pi_fintype, (degreeLTEquiv K _).finrank_eq, finrank_fin_fun,
      (AdjoinRoot.powerBasis (hm _)).finrank, AdjoinRoot.powerBasis_dim]
    exact h
  refine ⟨fun i ↦ y i, fun h0 ↦ hy0 (by ext i : 1; exact Subtype.ext congr($h0 i)),
    fun i ↦ (y i).2, fun j ↦ AdjoinRoot.mk_eq_zero.mp congr($hy j)⟩

end Polynomial
