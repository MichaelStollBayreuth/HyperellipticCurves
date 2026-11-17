/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.RingTheory.AdicCompletion.LocalRing`: `IsArtinianRing`, for the
-- statement of `IsLocalRing.of_isAdicComplete_of_isDomain`.
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Artinian.Defs

-- For the proof only: the lifting of idempotents along a nilpotent kernel
-- (`Mathlib.RingTheory.Idempotents`), along an adically complete ideal (the mirror of
-- `Mathlib.RingTheory.AdicCompletion.Basic`), and the nontrivial idempotent of an Artinian ring
-- with two maximal ideals (the mirror of `Mathlib.RingTheory.Artinian.Module`).
import HyperellipticCurves.Mathlib.RingTheory.AdicCompletion.Basic
import HyperellipticCurves.Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents

/-!
# A complete domain with Artinian quotient is local

## Main statements

* `IsLocalRing.of_isAdicComplete_of_isDomain`: a domain that is `I`-adically complete with
  Artinian quotient `A ⧸ I` is a local ring. Two distinct maximal ideals would produce a
  nontrivial idempotent of `(A ⧸ I) ⧸ nilradical`, which lifts along the nilradical and then,
  through the adic completeness, to a nontrivial idempotent of `A`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

variable {R : Type*} [CommRing R] {I : Ideal R}

-- Maximal ideals of `A` containing `I` stay maximal, and stay distinct, in `A ⧸ I`.
private theorem exists_ne_maximalSpectrum_quotient {A : Type*} [CommRing A] {I : Ideal A}
    (hIm : ∀ m : Ideal A, m.IsMaximal → I ≤ m) {m₀ m₁ : Ideal A}
    (hm₀ : m₀.IsMaximal) (hm₁ : m₁.IsMaximal) (hne : m₁ ≠ m₀) :
    ∃ M₁ M₀ : MaximalSpectrum (A ⧸ I), M₁ ≠ M₀ := by
  set ρ : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hmax (m : Ideal A) (hm : m.IsMaximal) : (m.map ρ).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIm m hm)
  have hcomap (m : Ideal A) (hm : m.IsMaximal) : (m.map ρ).comap ρ = m := by
    rw [Ideal.comap_map_of_surjective ρ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr (hIm m hm)
  refine ⟨⟨m₁.map ρ, hmax m₁ hm₁⟩, ⟨m₀.map ρ, hmax m₀ hm₀⟩, fun h ↦ hne ?_⟩
  rw [← hcomap m₁ hm₁, ← hcomap m₀ hm₀,
    show m₁.map ρ = m₀.map ρ from congrArg MaximalSpectrum.asIdeal h]

-- A nontrivial idempotent of `A ⧸ I` lifts along an adically complete `I`.
private theorem exists_isIdempotentElem_map_eq {A : Type*} [CommRing A] {I : Ideal A}
    [IsAdicComplete I A] {e₀ : A ⧸ I} (hide₀ : IsIdempotentElem e₀) :
    ∃ z : A, IsIdempotentElem z ∧ Ideal.Quotient.mk I z = e₀ := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I) e₀
  have haI : a ^ 2 - a ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ha, sq, hide₀.eq, sub_self]
  obtain ⟨z, hzid, hza⟩ := IsAdicComplete.exists_isIdempotentElem_of_sq_sub_mem I haI
  refine ⟨z, hzid, ?_⟩
  have h0 : Ideal.Quotient.mk I (z - a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hza
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ha]

/-- A domain that is `I`-adically complete with Artinian quotient `A ⧸ I` is a local ring:
two distinct maximal ideals (necessarily above `I`) would produce a nontrivial idempotent of
`(A ⧸ I) ⧸ nilradical` by the Artinian decomposition into fields, which lifts along the
nilradical and then, via Newton iteration (`e ↦ 3e² - 2e³`) through the adic completeness,
to a nontrivial idempotent of the domain `A`. -/
theorem IsLocalRing.of_isAdicComplete_of_isDomain {A : Type*} [CommRing A] [IsDomain A]
    {I : Ideal A} [IsAdicComplete I A] [IsArtinianRing (A ⧸ I)] :
    IsLocalRing A := by
  have hIm (m : Ideal A) (hm : m.IsMaximal) : I ≤ m :=
    (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨m₀, hm₀, fun m₁ hm₁ ↦ ?_⟩
  by_contra hne
  obtain ⟨M₁, M₀, hMne⟩ := exists_ne_maximalSpectrum_quotient hIm hm₀ hm₁ hne
  obtain ⟨e', hide', he'0, he'1⟩ := IsArtinianRing.exists_isIdempotentElem_ne_zero_ne_one_of_ne hMne
  obtain ⟨e₀, hide₀, he₀⟩ : ∃ e₀ : A ⧸ I, IsIdempotentElem e₀ ∧
      Ideal.Quotient.mk (nilradical (A ⧸ I)) e₀ = e' :=
    exists_isIdempotentElem_eq_of_ker_isNilpotent (f := Ideal.Quotient.mk (nilradical (A ⧸ I)))
      (fun x hx ↦ by rw [Ideal.mk_ker] at hx; exact hx) e'
      (by rw [RingHom.range_eq_top.mpr Ideal.Quotient.mk_surjective]; exact trivial) hide'
  obtain ⟨z, hzid, hmkz⟩ := exists_isIdempotentElem_map_eq hide₀
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hzid with rfl | rfl
  · exact he'0 (by rw [← he₀, ← hmkz, map_zero, map_zero])
  · exact he'1 (by rw [← he₀, ← hmkz, map_one, map_one])

end
