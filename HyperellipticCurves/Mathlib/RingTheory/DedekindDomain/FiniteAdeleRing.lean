/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: `Polynomial.HasSeparableReduction` (statement).
public import HyperellipticCurves.Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Separable reduction at almost all primes

## Main statements

* `Polynomial.finite_setOf_not_hasSeparableReduction`: a polynomial with nonzero discriminant over
  the fraction field of a Dedekind domain has separable reduction at all but finitely many primes.

Auxiliary material for the finiteness of the `2`-Selmer group of the `x - T` descent; upstreaming
candidate for Mathlib, next to `IsDedekindDomain.HeightOneSpectrum.Support.finite`.
-/

@[expose] public section

open Polynomial IsDedekindDomain

/-- A polynomial with nonzero discriminant has separable reduction at all but finitely many
primes: at the other primes a coefficient is not integral, or the leading coefficient or the
discriminant is not a unit, and each of these happens at finitely many primes
(`IsDedekindDomain.HeightOneSpectrum.Support.finite`). -/
theorem Polynomial.finite_setOf_not_hasSeparableReduction {R : Type*} [CommRing R]
    [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {f : K[X]}
    (hf : f ≠ 0) (hd : f.discr ≠ 0) :
    {v : HeightOneSpectrum R | ¬ f.HasSeparableReduction (v.valuation K)}.Finite := by
  open HeightOneSpectrum in
  refine ((f.support.finite_toSet.biUnion fun i _ ↦ Support.finite R (f.coeff i)).union
    ((Support.finite R f.leadingCoeff⁻¹).union ((Support.finite R f.discr).union
      (Support.finite R f.discr⁻¹)))).subset fun v hv ↦ ?_
  contrapose! hv
  simp only [Set.mem_union, Set.mem_iUnion, HeightOneSpectrum.Support, Set.mem_ofPred_eq,
    not_or, not_exists, not_lt] at hv
  have hle (i : ℕ) : v.valuation K (f.coeff i) ≤ 1 :=
    (em (i ∈ f.support)).elim (hv.1 i) fun hi ↦ by simp [notMem_support_iff.mp hi]
  exact not_not_intro ⟨hle, (hle _).antisymm <|
    ((v.valuation K).one_le_val_iff (leadingCoeff_ne_zero.mpr hf)).mpr hv.2.1,
      hv.2.2.1.antisymm <| ((v.valuation K).one_le_val_iff hd).mpr hv.2.2.2⟩

end
