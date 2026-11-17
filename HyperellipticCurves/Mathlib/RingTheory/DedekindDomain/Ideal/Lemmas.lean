/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Uniformizer certificates at maximal ideals of Dedekind domains

## Main statements

* `Ideal.exists_span_singleton_eq_mul_of_ne_bot`: at a nonzero maximal ideal `P` of a Dedekind
  domain there is an element `ϖ ∈ P ∖ P ^ 2`, recorded through the factorization
  `span {ϖ} = P * C` with `C ⊄ P`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A uniformizer certificate at a nonzero maximal ideal `P` of a Dedekind domain: an element
`ϖ ∈ P ∖ P ^ 2`, recorded through the factorization `span {ϖ} = P * C` with `C ⊄ P` of the
principal ideal it generates. -/
theorem Ideal.exists_span_singleton_eq_mul_of_ne_bot [IsDedekindDomain R] (P : Ideal R)
    [P.IsMaximal] (hP : P ≠ ⊥) :
    ∃ (ϖ : R) (C : Ideal R), Ideal.span {ϖ} = P * C ∧ ¬ C ≤ P := by
  obtain ⟨ϖ, hϖ, hϖ2⟩ :=
    IsConcreteLE.exists_of_lt (Ideal.pow_lt_self P hP (Ideal.IsMaximal.ne_top ‹_›) 2 le_rfl)
  obtain ⟨C, hC⟩ : P ∣ Ideal.span {ϖ} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hϖ))
  refine ⟨ϖ, C, hC, fun hle ↦ hϖ2 ?_⟩
  obtain ⟨C', hC'⟩ := Ideal.dvd_iff_le.mpr hle
  exact Ideal.le_of_dvd ⟨C', by rw [hC, hC', sq, mul_assoc]⟩ (Ideal.mem_span_singleton_self ϖ)

end
