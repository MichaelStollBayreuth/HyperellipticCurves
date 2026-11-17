/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.HypBaseChangeEmult

import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Stability of intrinsic multiplicities under base change

The multiplicity of a rational point ideal in an ideal of the coordinate ring is unchanged under
base change (`ChabautyColeman.emultiplicity_pointIdeal_map_baseChangeTo`). The main theorems do
not depend on it: the reduction homomorphism compares divisors through point factorization over
the algebraically closed residue field and ord-matching on disks instead.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-! ### Stability of intrinsic multiplicities -/

section Stability

open IsDedekindDomain

/-- The multiplicity of a prime `P` in a nonzero ideal `I` of a Dedekind domain is the sum, over
the (finitely many) height-one primes `v` in the support of `I`, of the multiplicity of `P` in the
maximal power of `v` dividing `I`. -/
private theorem emultiplicity_eq_finsetSum_maxPowDividing {R : Type*} [CommRing R]
    [IsDedekindDomain R] {P : Ideal R} (hP : Prime P) {I : Ideal R} (hI : I ≠ 0)
    (hfin : (Function.mulSupport fun v : HeightOneSpectrum R ↦ v.maxPowDividing I).Finite) :
    emultiplicity P I = ∑ v ∈ hfin.toFinset, emultiplicity P (v.maxPowDividing I) := by
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI, finprod_eq_prod _ hfin]
  rw [Finset.emultiplicity_prod hP]

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {f : K[X]} {g : L[X]}
  (hg : f.map (algebraMap K L) = g)
  [NeZero (2 : K)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]
  [NeZero (2 : L)] [Fact (Odd g.natDegree)] [Fact (Squarefree g)]

/-- Per height-one prime `v`: base change preserves the multiplicity of the point ideal in the
maximal power of `v` dividing `I`. The point ideal is maximal, so `v = P` contributes its self
multiplicity (unchanged since both point ideals are maximal) and every other maximal `v`
contributes `0` (its extension cannot contain the base-changed point ideal, as a witness
non-vanishing at the point stays non-vanishing after base change). -/
private theorem emultiplicity_map_baseChangeTo_maxPowDividing {x y : K} (h : y ^ 2 = f.eval x)
    {I : Ideal (HypRing K f)} (hI : I ≠ 0) (v : HeightOneSpectrum (HypRing K f)) :
    emultiplicity ((pointIdeal f x y).map (HypRing.baseChangeTo f hg))
        ((v.maxPowDividing I).map (HypRing.baseChangeTo f hg))
      = emultiplicity (pointIdeal f x y) (v.maxPowDividing I) := by
  set φ := algebraMap K L
  set bc := HypRing.baseChangeTo f hg with hbc
  set P := pointIdeal f x y with hP_def
  have hL : (φ y) ^ 2 = g.eval (φ x) := by rw [← hg, eval_map, eval₂_at_apply, ← map_pow, h]
  have hPbc : P.map bc = pointIdeal g (φ x) (φ y) := pointIdeal_baseChangeTo f hg x y
  have hP : Prime P :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x y) (pointIdeal_isPrime h)
  have hP' : Prime (P.map bc) := by
    rw [hPbc]
    exact Ideal.prime_of_isPrime (pointIdeal_ne_bot g (φ x) (φ y)) (pointIdeal_isPrime hL)
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, Ideal.map_pow,
    emultiplicity_pow hP', emultiplicity_pow hP]
  congr 1
  by_cases hv : v.asIdeal = P
  · rw [hv, hPbc, Ideal.emultiplicity_self_of_ne_top (pointIdeal_isMaximal hL).ne_top
      (pointIdeal_ne_bot g (φ x) (φ y)),
      Ideal.emultiplicity_self_of_ne_top (pointIdeal_isMaximal h).ne_top (pointIdeal_ne_bot f x y)]
  · have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    rw [Ideal.emultiplicity_eq_zero_of_isMaximal_of_ne (pointIdeal_isMaximal h) hvmax hv,
      emultiplicity_eq_zero, Ideal.dvd_iff_le]
    intro hle
    obtain ⟨w, hwv, hwP⟩ := IsConcreteLE.not_le_iff_exists.mp
      (fun hle' ↦ hv (hvmax.eq_of_le (pointIdeal_isMaximal h).ne_top hle'))
    have hmem : bc w ∈ P.map bc := hle (Ideal.mem_map_of_mem _ hwv)
    rw [hPbc, pointIdeal_eq_ker hL, RingHom.mem_ker,
      evalHom_baseChangeTo f hg h hL] at hmem
    refine hwP ?_
    rw [hP_def, pointIdeal_eq_ker h, RingHom.mem_ker]
    exact (map_eq_zero_iff φ φ.injective).mp hmem

/-- Intrinsic multiplicities at rational points are stable under base change. -/
theorem emultiplicity_pointIdeal_map_baseChangeTo {x y : K} (h : y ^ 2 = f.eval x)
    {I : Ideal (HypRing K f)} (hI : I ≠ 0) :
    emultiplicity (pointIdeal g (algebraMap K L x) (algebraMap K L y))
        (I.map (HypRing.baseChangeTo f hg))
      = emultiplicity (pointIdeal f x y) I := by
  set bc := HypRing.baseChangeTo f hg with hbc
  set P := pointIdeal f x y with hP_def
  have hPbc : P.map bc = pointIdeal g (algebraMap K L x) (algebraMap K L y) :=
    pointIdeal_baseChangeTo f hg x y
  rw [← hPbc]
  have hL : (algebraMap K L y) ^ 2 = g.eval (algebraMap K L x) := by
    rw [← hg, eval_map, eval₂_at_apply, ← map_pow, h]
  have hP : Prime P :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x y) (pointIdeal_isPrime h)
  have hP' : Prime (P.map bc) := by
    rw [hPbc]
    exact Ideal.prime_of_isPrime (pointIdeal_ne_bot g _ _) (pointIdeal_isPrime hL)
  have hfin := Ideal.hasFiniteMulSupport hI
  have hmapprod : (∏ v ∈ hfin.toFinset, v.maxPowDividing I).map bc
      = ∏ v ∈ hfin.toFinset, (v.maxPowDividing I).map bc :=
    map_prod (Ideal.mapHom bc) _ _
  have hLHS : emultiplicity (P.map bc) (I.map bc)
      = ∑ v ∈ hfin.toFinset, emultiplicity (P.map bc) ((v.maxPowDividing I).map bc) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI, finprod_eq_prod _ hfin]
    rw [hmapprod, Finset.emultiplicity_prod hP']
  rw [hLHS, emultiplicity_eq_finsetSum_maxPowDividing hP hI hfin]
  exact Finset.sum_congr rfl fun v _ ↦ emultiplicity_map_baseChangeTo_maxPowDividing hg h hI v

end Stability


end ChabautyColeman

end
