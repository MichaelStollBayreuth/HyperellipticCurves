/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: the primes above a prime, in the statement.
public import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# The multiplicity of a prime in a relative norm

## Main statements

* `Ideal.multiplicity_relNorm`: the multiplicity of a prime `v` of `R` in the relative norm of a
  nonzero ideal `I` of `S` is the sum of the multiplicities in `I` of the primes `w` of `S` above
  `v`, weighted by their inertia degrees.

Auxiliary material for the valuation of a norm in the Selmer groups of the `x - T` descent;
upstreaming candidate for Mathlib.
-/

@[expose] public section

open IsDedekindDomain HeightOneSpectrum

namespace Ideal

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

-- The case of a prime ideal in `Ideal.multiplicity_relNorm`: the multiplicity of `v` in the norm
-- of `w₀` is the inertia degree of `w₀` if `w₀` lies above `v`, and `0` otherwise.
private theorem multiplicity_relNorm_asIdeal [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (v : HeightOneSpectrum R) (w₀ : HeightOneSpectrum S) :
    multiplicity v.asIdeal (relNorm R w₀.asIdeal) = ∑ᶠ w ∈ primesAbove R S {v},
      w.asIdeal.inertiaDeg R * multiplicity w.asIdeal w₀.asIdeal := by
  classical
  rw [relNorm_eq_pow_of_isMaximal w₀.asIdeal (w₀.under R).asIdeal,
    finsum_eq_single _ w₀ fun w hw ↦ by simp [multiplicity_asIdeal_of_ne hw],
    w₀.irreducible.multiplicity_self, mul_one, finsum_eq_if, mem_primesAbove_singleton_iff]
  split_ifs with h
  · exact h ▸ multiplicity_pow_self_of_prime v.prime _
  · exact multiplicity_eq_zero_of_not_dvd fun hd ↦
      h (asIdeal_dvd_asIdeal_iff.mp (v.prime.dvd_of_dvd_pow hd)).symm

/-- The multiplicity of a prime `v` of `R` in the relative norm of a nonzero ideal `I` of `S` is
the sum of the multiplicities in `I` of the primes `w` of `S` above `v`, weighted by their inertia
degrees. -/
theorem multiplicity_relNorm [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (v : HeightOneSpectrum R) {I : Ideal S} (hI : I ≠ ⊥) :
    multiplicity v.asIdeal (relNorm R I) = ∑ᶠ w ∈ primesAbove R S {v},
      w.asIdeal.inertiaDeg R * multiplicity w.asIdeal I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ I hu => simp [isUnit_iff.mp hu, ← one_eq_top]
  | h₃ I P hI0 hP ih =>
    obtain ⟨w₀, rfl⟩ : ∃ w₀ : HeightOneSpectrum S, w₀.asIdeal = P :=
      ⟨⟨P, isPrime_of_prime hP, hP.ne_zero⟩, rfl⟩
    have hN (J : Ideal S) (hJ : J ≠ ⊥) : relNorm R J ≠ ⊥ := relNorm_eq_bot_iff.not.mpr hJ
    rw [map_mul, multiplicity_asIdeal_mul v (hN _ w₀.ne_bot) (hN _ hI0), ih hI0,
      multiplicity_relNorm_asIdeal, ← finsum_mem_add_distrib (primesAbove_singleton_finite v)]
    refine finsum_mem_congr rfl fun w _ ↦ ?_
    rw [multiplicity_asIdeal_mul w w₀.ne_bot hI0, mul_add]

end Ideal
