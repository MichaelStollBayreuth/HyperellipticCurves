/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Interpolation through unit-separated points

## Main statements

* `Polynomial.exists_degree_lt_eval_eq`: over any commutative ring, values prescribed at points
  whose differences are units are attained by a polynomial of degree below
  `∏ i, (X - C (x i))`. Unit separation makes the linear factors pairwise comaximal, so the
  Chinese remainder theorem applies.
* `Polynomial.eq_of_degree_sub_lt_card_of_eval_eq`: two polynomials agreeing at more points than
  the degree of their difference are equal; a form of
  `Polynomial.eq_of_degree_sub_lt_of_eval_index_eq` for an injective family indexed by a
  `Fintype`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

open Function in
/-- **Interpolation through unit-separated points**: over any commutative ring, values
prescribed at points whose differences are units are attained by a polynomial of degree below
`∏ (X - C (x i))`. Unit separation makes the linear factors pairwise comaximal, so the
Chinese remainder theorem applies. -/
theorem exists_degree_lt_eval_eq {R : Type*} [CommRing R] [Nontrivial R] {ι : Type*} [Fintype ι]
    {x : ι → R} (hx : ∀ i j, i ≠ j → IsUnit (x i - x j)) (y : ι → R) :
    ∃ w : R[X], w.degree < (∏ i, (X - C (x i))).degree ∧ ∀ i, w.eval (x i) = y i := by
  set u : R[X] := ∏ i, (X - C (x i))
  have hum : u.Monic := monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)
  have hpair : Pairwise (IsCoprime on fun i : ι ↦ Ideal.span {X - C (x i)}) := fun i j hij ↦ by
    rw [onFun, Ideal.isCoprime_span_singleton_iff]
    exact isCoprime_X_sub_C_of_isUnit_sub (hx i j hij)
  obtain ⟨w, hw⟩ := Ideal.exists_forall_sub_mem_ideal hpair fun i ↦ C (y i)
  refine ⟨w %ₘ u, degree_modByMonic_lt w hum, fun i ↦ ?_⟩
  have hu0 : u.eval (x i) = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      (by rw [eval_sub, eval_X, eval_C, sub_self])
  have heq := congrArg (Polynomial.eval (x i)) (modByMonic_add_div w u)
  rw [eval_add, eval_mul, hu0, zero_mul, add_zero] at heq
  have h0 := dvd_iff_isRoot.mp (Ideal.mem_span_singleton.mp (hw i))
  rw [IsRoot, eval_sub, eval_C] at h0
  exact heq.trans (sub_eq_zero.mp h0)

/-- Two polynomials agreeing at more points than the degree of their difference are equal.
Thin adapter (NOT Mathlib-bound) over `Polynomial.eq_of_degree_sub_lt_of_eval_index_eq`,
in the `Function.Injective`/`Fintype` currency the call sites spend. -/
theorem eq_of_degree_sub_lt_card_of_eval_eq {R : Type*} [CommRing R] [IsDomain R] {p q : R[X]}
    {ι : Type*} [Fintype ι] {x : ι → R} (hx : Function.Injective x)
    (heval : ∀ i, p.eval (x i) = q.eval (x i)) (hdeg : (p - q).degree < Fintype.card ι) :
    p = q :=
  Polynomial.eq_of_degree_sub_lt_of_eval_index_eq Finset.univ hx.injOn
    (by rw [Finset.card_univ]; exact hdeg) fun i _ ↦ heval i

end Polynomial

end
