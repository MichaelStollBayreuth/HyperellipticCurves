/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Uniformizers, multiplicities, and the primes above a set of primes in Dedekind domains

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.primesAbove R B S`: the primes of `B` above the primes in
  `S`.
* `IsDedekindDomain.HeightOneSpectrum.comapOfNeBot`: the contraction of a height one prime along a
  ring homomorphism, when it is nonzero.

## Main statements

* `Ideal.exists_span_singleton_eq_mul_of_ne_bot`: at a nonzero maximal ideal `P` of a Dedekind
  domain there is an element `ϖ ∈ P ∖ P ^ 2`, recorded through the factorization
  `span {ϖ} = P * C` with `C ⊄ P`.
* `IsDedekindDomain.HeightOneSpectrum.le_count_iff_le`,
  `IsDedekindDomain.HeightOneSpectrum.le_count_iff`: the multiplicity of `v` in an ideal as a
  divisibility.
* `IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff`: for an integral extension, `w` lies
  above `S` exactly when `w.under R ∈ S`.
* `IsDedekindDomain.HeightOneSpectrum.primesAbove_finite`: only finitely many primes lie above a
  finite set of primes.
* `IsDedekindDomain.HeightOneSpectrum.primesAbove_singleton_finite`,
  `IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_singleton_iff`: the case of a single prime.

The declarations about `primesAbove` are vendored from EllipticCurves
(`EllipticCurves/Mathlib/Basic.lean` and `EllipticCurves/Mathlib/SIntegers.lean`).

Auxiliary material for the formalization of the Chabauty–Coleman bound and of `2`-descent for
hyperelliptic curves; upstreaming candidates for Mathlib.
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

namespace IsDedekindDomain.HeightOneSpectrum

section Count

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

/-- The multiplicity of `v` in `J` is at least `k` iff `v ^ k` divides `J`. -/
theorem le_count_iff_le {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

/-- The multiplicity of `v` in `(x)` is at least `k` iff `x ∈ v ^ k`. -/
theorem le_count_iff {x : A} (hx : x ≠ 0) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors ↔
      x ∈ v.asIdeal ^ k := by
  rw [v.le_count_iff_le (fun h ↦ hx (Ideal.span_singleton_eq_bot.mp h)) k,
    Ideal.span_singleton_le_iff_mem]

variable {v} in
/-- A height one prime is not contained in any other one. -/
theorem exists_mem_notMem_of_ne {w : HeightOneSpectrum A} (h : w ≠ v) :
    ∃ a ∈ v.asIdeal, a ∉ w.asIdeal := by
  by_contra! hc
  exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)

end Count

section Comap

/-- The height one prime `w.asIdeal.comap ψ` of `B`, for a ring homomorphism `ψ : B →+* C` under
which the contraction of `w` is nonzero. -/
@[simps]
def comapOfNeBot {B C : Type*} [CommRing B] [CommRing C] (ψ : B →+* C) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) : HeightOneSpectrum B where
  asIdeal := w.asIdeal.comap ψ
  isPrime := w.isPrime.comap ψ
  ne_bot := hne

end Comap

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (B : Type*) [CommRing B]
  [IsDedekindDomain B] [Algebra R B]

/-- The height one primes of `B` lying above a set `S` of height one primes of `R`. -/
def primesAbove (S : Set (HeightOneSpectrum R)) : Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}

instance instLiesOverUnder [Algebra.IsIntegral R B] (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.under R).asIdeal :=
  Ideal.over_under ..

theorem mem_primesAbove_iff [Algebra.IsIntegral R B] (S : Set (HeightOneSpectrum R))
    (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ w.under R ∈ S :=
  ⟨fun ⟨v, hv, hva⟩ ↦ (HeightOneSpectrum.ext hva.symm : w.under R = v) ▸ hv,
    fun hw ↦ ⟨w.under R, hw, rfl⟩⟩

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`: each fiber injects
into `Ideal.primesOver`, which is finite for a Dedekind extension. -/
theorem primesAbove_finite [Algebra.IsIntegral R B] [Module.IsTorsionFree R B]
    {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    (primesAbove R B S).Finite := by
  have hsub : primesAbove R B S ⊆
      ⋃ v ∈ S, {w : HeightOneSpectrum B | w.asIdeal ∈ v.asIdeal.primesOver B} :=
    fun w ⟨v, hv, hva⟩ ↦ Set.mem_biUnion hv ⟨w.isPrime, ⟨hva⟩⟩
  exact (hS.biUnion fun v _ ↦
    (primesOver_finite v.asIdeal B).preimage asIdeal_injective.injOn).subset hsub

variable {R B}

theorem primesAbove_singleton_finite [Algebra.IsIntegral R B] [Module.IsTorsionFree R B]
    (v : HeightOneSpectrum R) : (primesAbove R B {v}).Finite :=
  primesAbove_finite R B (Set.finite_singleton v)

theorem mem_primesAbove_singleton_iff [Algebra.IsIntegral R B] {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum B} :
    w ∈ primesAbove R B {v} ↔ w.under R = v := mem_primesAbove_iff R B {v} w

end IsDedekindDomain.HeightOneSpectrum

end
