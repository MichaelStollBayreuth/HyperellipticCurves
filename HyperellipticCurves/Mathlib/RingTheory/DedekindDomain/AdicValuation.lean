/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling, for the statements: the completions `adicCompletion`, `valuationOfNeZero`
-- and discrete valuation rings.
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

-- For the proofs only.
import HyperellipticCurves.Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Adic valuations of units, and adic completions of the fraction field

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_of_isUnit`: the `v`-adic valuation of a
  unit is `1`.
* `IsDedekindDomain.HeightOneSpectrum.instCharZeroAdicCompletion`: the completion of a field of
  characteristic `0` has characteristic `0`.
* `IsDedekindDomain.HeightOneSpectrum.valuation_maximalIdeal_adicCompletionIntegers`,
  `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_maximalIdeal_adicCompletionIntegers`: the
  valuation of the maximal ideal of `𝒪_v` is the valuation of `K_v`.
* `IsDedekindDomain.HeightOneSpectrum.valuation_adicCompletion_algebraMap`: every height one prime
  of `𝒪_v` induces `v` on `K`.

Auxiliary material for the formalization of the Chabauty–Coleman bound and of `2`-descent for
hyperelliptic curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R)

/-- The `v`-adic valuation of a unit is `1`. -/
theorem intValuation_eq_one_of_isUnit {a : R} (ha : IsUnit a) : v.intValuation a = 1 :=
  intValuation_eq_one_iff.mpr fun hmem ↦ v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ha)

end IsDedekindDomain.HeightOneSpectrum

open WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

instance instCharZeroAdicCompletion [CharZero K] : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

/-- An irreducible element of the ring of integers of a completion has valuation `exp (-1)`. -/
theorem valued_irreducible_adicCompletionIntegers {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (π : v.adicCompletion K) = exp (-1) := by
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni

theorem intValuation_maximalIdeal_adicCompletionIntegers (y : v.adicCompletionIntegers K) :
    (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).intValuation y =
      Valued.v (y : v.adicCompletion K) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  have hu : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mp u.isUnit
  have hu' : (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).intValuation
      (u : v.adicCompletionIntegers K) = 1 :=
    intValuation_eq_one_iff.mpr (IsLocalRing.notMem_maximalIdeal.mpr u.isUnit)
  simp [hu, hu', v.valued_irreducible_adicCompletionIntegers hπ,
    (IsDiscreteValuationRing.maximalIdeal _).intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq]

/-- The valuation of the height one prime of the ring of integers `𝒪_v` of `K_v` (a discrete
valuation ring) is the valuation of `K_v`. -/
theorem valuation_maximalIdeal_adicCompletionIntegers (x : v.adicCompletion K) :
    (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
      (v.adicCompletion K) x = Valued.v x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := v.adicCompletionIntegers K) x
  simp only [map_div₀, valuation_of_algebraMap, intValuation_maximalIdeal_adicCompletionIntegers]
  rfl

theorem valuationOfNeZero_maximalIdeal_adicCompletionIntegers (u : Kˣ) :
    (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuationOfNeZero
      (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u) = v.valuationOfNeZero u := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, valuationOfNeZero_eq, Units.coe_map,
    valuation_maximalIdeal_adicCompletionIntegers]
  exact v.valuedAdicCompletion_eq_valuation' _

/-- Any height one prime `P` of `𝒪_v` (its maximal ideal) induces on `K` the valuation `v`. -/
theorem valuation_adicCompletion_algebraMap (P : HeightOneSpectrum (v.adicCompletionIntegers K))
    (z : K) :
    P.valuation (v.adicCompletion K) (algebraMap K (v.adicCompletion K) z) = v.valuation K z := by
  rw [P.eq_maximalIdeal, valuation_maximalIdeal_adicCompletionIntegers]
  exact v.valuedAdicCompletion_eq_valuation' z

end IsDedekindDomain.HeightOneSpectrum

end
