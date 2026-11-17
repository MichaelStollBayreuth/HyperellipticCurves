/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Valuations in an extension of Dedekind domains

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`: the extension `K_v →+* L_w` of
  adic completions along `w ∣ v` (adapted from FLT, by Buzzard, Yang and Jasper).

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_le_one`,
  `IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_eq_one`: if an element of `K` is
  integral (resp. a unit) for the valuation of the prime of `R` below `w`, then its image in `L` is
  integral (resp. a unit) for the valuation of `w`.
* `IsDedekindDomain.HeightOneSpectrum.exists_valuation_map_eq_pow`:
  `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` for compatible ring homomorphisms
  `ψ : B →+* C` and `φ : L →+* N`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension_algebraMap`,
  `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionExtension`: the extension restricts to
  `K → L`, and the valuation of `L_w` restricts to the `e`-th power of that of `K_v`.

Auxiliary material for the point lemma and the semilocal comparison of the `x - T` descent;
upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Algebra.IsIntegral R B] [Module.IsTorsionFree R B] (L : Type*) [Field L] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L]

theorem valuation_algebraMap_le_one (w : HeightOneSpectrum B) {z : K}
    (hz : (w.under R).valuation K z ≤ 1) : w.valuation L (algebraMap K L z) ≤ 1 := by
  rw [← valuation_liesOver L (w.under R) w]
  exact pow_le_one₀ zero_le hz

theorem valuation_algebraMap_eq_one (w : HeightOneSpectrum B) {z : K}
    (hz : (w.under R).valuation K z = 1) : w.valuation L (algebraMap K L z) = 1 := by
  rw [← valuation_liesOver L (w.under R) w, hz, one_pow]

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

section Map

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
  {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L] [Field N] [Algebra C N]
  [IsFractionRing C N]

/-- For compatible embeddings `ψ : B →+* C` of Dedekind domains and `φ : L →+* N` of their
fraction fields, the `w`-adic valuation of `φ x` is a fixed power (the ramification index) of the
valuation of `x` at the contraction of `w`: `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`
for the algebras given by `ψ` and `φ`. -/
theorem exists_valuation_map_eq_pow {φ : L →+* N} {ψ : B →+* C}
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L)) {w : HeightOneSpectrum C}
    (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ x : L, w.valuation N (φ x) = (comapOfNeBot ψ w hne).valuation L x ^ e := by
  have hψ : Function.Injective ψ := .of_comp (f := algebraMap C N) <| by
    rw [← RingHom.coe_comp, hcomp]
    exact φ.injective.comp (IsFractionRing.injective B L)
  let : Algebra B C := ψ.toAlgebra
  let : Algebra L N := φ.toAlgebra
  let : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have : IsScalarTower B C N := .of_algebraMap_eq fun x ↦ (RingHom.congr_fun hcomp x).symm
  have : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨rfl⟩
  exact ⟨_, fun x ↦ (valuation_liesOver N (comapOfNeBot ψ w hne) w x).symm⟩

end Map

-- The valuation of the completion of `K` at a height one prime is continuous.
open WithZero WithZeroTopology in
private theorem continuous_valued_completion {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    Continuous (Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰) :=
  Valued.continuous_valuation_of_surjective <|
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)

section Extension

variable {A : Type*} (K L : Type*) {B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B]
  [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B] [Field K] [Field L]
  [Algebra K L] [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
  (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- The extension of adic completions along `w ∣ v`: the ring homomorphism `K_v →+* L_w`
extending `K → L` continuously. Adapted from the FLT project
(`FLT.DedekindDomain.Completion.BaseChange`, by Kevin Buzzard, Andrew Yang and Matthew Jasper). -/
noncomputable def adicCompletionExtension : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom

theorem toCompletion_adicCompletionExtension (x : v.adicCompletion K) :
    (adicCompletionExtension K L v w x).toCompletion =
      UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous x.toCompletion :=
  rfl

@[simp]
theorem adicCompletionExtension_algebraMap (x : K) :
    adicCompletionExtension K L v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  ext
  rw [toCompletion_adicCompletionExtension, algebraMap_adicCompletion_toCompletion]
  exact UniformSpace.Completion.mapRingHom_coe _ ((WithVal.equiv (v.valuation K)).symm x)

open WithZero WithZeroTopology in
/-- The valuation of `L_w` restricted along `K_v →+* L_w` is the valuation of `K_v` raised to
the ramification index of `w` over `v`. Adapted from FLT's `valued_adicCompletionSemialgHom`
(Buzzard, Yang, Jasper). -/
theorem valued_adicCompletionExtension (x : v.adicCompletion K) :
    Valued.v (adicCompletionExtension K L v w x) = Valued.v x ^ w.asIdeal.ramificationIdx A := by
  rw [← adicCompletion.valued_toCompletion_apply, toCompletion_adicCompletionExtension,
    ← adicCompletion.valued_toCompletion_apply]
  induction x.toCompletion using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_valued_completion w).comp
      UniformSpace.Completion.continuous_map) ((continuous_valued_completion v).pow _)
  | ih a =>
    rw [UniformSpace.Completion.mapRingHom_coe, Valued.valuedCompletion_apply,
      Valued.valuedCompletion_apply]
    exact (valuation_liesOver L v w (WithVal.equiv (v.valuation K) a)).symm

end Extension

end IsDedekindDomain.HeightOneSpectrum
