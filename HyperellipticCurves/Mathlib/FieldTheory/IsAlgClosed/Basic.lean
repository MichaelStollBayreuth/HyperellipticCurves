/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraic closedness along ring isomorphisms, and coprimality from disjoint zero sets

`IsAlgClosed.of_ringEquiv'` is the universe-polymorphic form of Mathlib's
`IsAlgClosed.of_ringEquiv`, whose statement constrains the two fields to lie in the same universe
although its proof (reproduced verbatim here) never uses that. It should replace
`IsAlgClosed.of_ringEquiv` upstream.

## Main statements

* `IsAlgClosed.of_ringEquiv'`: a field isomorphic to an algebraically closed field is
  algebraically closed.
* `Polynomial.isCoprime_of_forall_eval_ne_zero`: over an algebraically closed field, two
  polynomials without common zero are coprime.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial

/-- A field isomorphic to an algebraically closed field is algebraically closed. This is
`IsAlgClosed.of_ringEquiv` without its same-universe restriction. -/
theorem IsAlgClosed.of_ringEquiv' {k k' : Type*} [Field k] [Field k'] [IsAlgClosed k]
    (e : k ≃+* k') : IsAlgClosed k' := by
  refine IsAlgClosed.of_exists_root _ fun q hqm hq ↦ ?_
  have hqe : degree (q.map e.symm.toRingHom) ≠ 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hq)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (k := k) (q.map e.symm.toRingHom) hqe
  refine ⟨e x, ?_⟩
  rw [IsRoot] at hx
  refine e.symm.injective ?_
  rw [map_zero, ← hx]
  clear hx hqe hq hqm
  induction q using Polynomial.induction_on <;> simp_all

namespace Polynomial

variable {K : Type*} [Field K]

/-- Coprimality over an algebraically closed field from disjoint zero sets. -/
theorem isCoprime_of_forall_eval_ne_zero [IsAlgClosed K] {p q : K[X]} (hq : q ≠ 0)
    (h : ∀ x, p.eval x = 0 → q.eval x ≠ 0) : IsCoprime p q := by
  classical
  by_contra hcop
  rw [← EuclideanDomain.gcd_isUnit_iff] at hcop
  have hg0 : EuclideanDomain.gcd p q ≠ 0 := fun h0 ↦
    hq (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (EuclideanDomain.gcd p q)
    (fun hdeg ↦ hcop (isUnit_iff_degree_eq_zero.mpr hdeg))
  exact h x (eval_eq_zero_of_dvd_of_eval_eq_zero (EuclideanDomain.gcd_dvd_left p q) hx)
    (eval_eq_zero_of_dvd_of_eval_eq_zero (EuclideanDomain.gcd_dvd_right p q) hx)

end Polynomial

end
