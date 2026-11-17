/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Descent.Selmer
public import HyperellipticCurves.Mathlib.FieldTheory.Perfect
public import HyperellipticCurves.Mathlib.NumberTheory.RamificationInertia.Valuation
public import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.AdicValuation

import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot

/-!
# Local to global for the group `A(S, n)`

Let `K` be the fraction field of a Dedekind domain `R`, of characteristic `0`, let `f` be a
squarefree polynomial over `K` and let `S` be a set of primes of `R`. A class of
`(K[X] ⧸ (f))ˣ` modulo `n`-th powers lies in `A(S, n)` (`AdjoinRoot.selmerGroup`) as soon as its
image over the completion `K_v` is unramified at every prime `v ∉ S`. This is the step from the
local images to `A(Σ, 2)` in the inclusion of the `2`-Selmer group in `A(Σ, 2)`
(`ChabautyColeman.HypJac.selmerGroupTwo_le_selmerGroup`).

A prime `w` above `v` of a field factor `L = K[X] ⧸ (p)` gives the monic irreducible factor `q` of
`f` over `K_v` that vanishes at the image of the root of `p` in the completion `L_w`, through the
extension of completions `K_v → L_w` (`IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`).
The induced map `K_v[X] ⧸ (q) → L_w` sends the integral closure of the valuation ring `𝒪_v` into
the valuation ring `𝒪_w` (`Valuation.le_one_of_isIntegral`), the maximal ideal of `𝒪_w` contracts to
a prime of that integral closure, and the order at `w` of a unit is a multiple of its order at this
prime (`IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map`).

## Main statements

* `AdjoinRoot.mem_selmerGroup_of_forall_adicCompletion`: a class whose images over the completions
  `K_v`, `v ∉ S`, are unramified lies in `A(S, n)`.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5

Adapted from `WeierstrassCurve.Affine.mem_selmerGroupA_of_forall_localRes` of EllipticCurves
(`EllipticCurves/SelmerGroup.lean`, section `Semilocal`), for general `n` and a general Dedekind
domain.
-/

@[expose] public section

open Polynomial IsDedekindDomain

namespace AdjoinRoot

open HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K] {f : K[X]}

section Completion

variable (p : f.Factors) (v : HeightOneSpectrum R)
  (w : HeightOneSpectrum (integralClosure R (AdjoinRoot (p : K[X]))))
  [w.asIdeal.LiesOver v.asIdeal]

-- The image of `g` over `K_v`, evaluated at the image in `L_w` of the root of `p`, is the image
-- of the class of `g` in `L = K[X] ⧸ (p)`.
private theorem eval₂_map_adicCompletionExtension (g : K[X]) :
    (g.map (algebraMap K (v.adicCompletion K))).eval₂
        (adicCompletionExtension K (AdjoinRoot (p : K[X])) v w)
        (algebraMap _ (w.adicCompletion (AdjoinRoot (p : K[X]))) (root (p : K[X]))) =
      algebraMap _ (w.adicCompletion (AdjoinRoot (p : K[X]))) (mk (p : K[X]) g) := by
  rw [eval₂_map, ← aeval_eq, aeval_def, hom_eval₂]
  exact congr(eval₂ $(RingHom.ext fun c ↦ adicCompletionExtension_algebraMap ..) _ g)

-- The image in `L_w` of the root of `p` is a root of `f` over `K_v`.
private theorem eval₂_map_adicCompletionExtension_eq_zero :
    (f.map (algebraMap K (v.adicCompletion K))).eval₂
        (adicCompletionExtension K (AdjoinRoot (p : K[X])) v w)
        (algebraMap _ (w.adicCompletion (AdjoinRoot (p : K[X]))) (root (p : K[X]))) = 0 := by
  rw [eval₂_map_adicCompletionExtension, mk_eq_zero.mpr p.dvd, map_zero]

section Factor

variable {p v w} (q : (f.map (algebraMap K (v.adicCompletion K))).Factors)
  (hq : (q : (v.adicCompletion K)[X]).eval₂ (adicCompletionExtension K (AdjoinRoot (p : K[X])) v w)
    (algebraMap _ (w.adicCompletion (AdjoinRoot (p : K[X]))) (root (p : K[X]))) = 0)

-- The lift `K_v[X] ⧸ (q) → L_w` maps the integral closure of `𝒪_v` into `𝒪_w`.
private theorem valued_lift_le_one
    (x : integralClosure (v.adicCompletionIntegers K) (AdjoinRoot (q : (v.adicCompletion K)[X]))) :
    Valued.v (lift _ _ hq (x : AdjoinRoot (q : (v.adicCompletion K)[X]))) ≤ 1 := by
  refine (Valued.v.comap (lift _ _ hq)).le_one_of_isIntegral (fun c ↦ ?_) x.2
  rw [Valuation.comap_apply, algebraMap_eq', RingHom.comp_apply, lift_of,
    valued_adicCompletionExtension]
  exact pow_le_one₀ zero_le c.2

-- The lift `K_v[X] ⧸ (q) → L_w`, restricted to the integral closure of `𝒪_v` and to `𝒪_w`.
private noncomputable def integralClosureLift :
    integralClosure (v.adicCompletionIntegers K) (AdjoinRoot (q : (v.adicCompletion K)[X])) →+*
      w.adicCompletionIntegers (AdjoinRoot (p : K[X])) :=
  ((lift _ _ hq).comp (algebraMap _ _)).codRestrict _ (valued_lift_le_one q hq)

private theorem coe_integralClosureLift
    (x : integralClosure (v.adicCompletionIntegers K) (AdjoinRoot (q : (v.adicCompletion K)[X]))) :
    (integralClosureLift q hq x : w.adicCompletion (AdjoinRoot (p : K[X]))) =
      lift _ _ hq (x : AdjoinRoot (q : (v.adicCompletion K)[X])) :=
  rfl

-- The maximal ideal of `𝒪_w` contracts to a nonzero prime of the integral closure of `𝒪_v`: it
-- contains the image of a nonzero element of the maximal ideal of `𝒪_v`.
private theorem comap_integralClosureLift_ne_bot :
    (IsDiscreteValuationRing.maximalIdeal
      (w.adicCompletionIntegers (AdjoinRoot (p : K[X])))).asIdeal.comap
        (integralClosureLift q hq) ≠ ⊥ := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K))
  refine (Submodule.ne_bot_iff _).mpr ⟨algebraMap _ _ π, ?_,
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hπ0⟩
  rw [Ideal.mem_comap]
  refine (Valuation.mem_maximalIdeal_iff (v := Valued.v)).mpr ?_
  rw [coe_integralClosureLift, Subalgebra.coe_algebraMap, algebraMap_eq', RingHom.comp_apply,
    lift_of, valued_adicCompletionExtension]
  exact pow_lt_one₀ zero_le ((Valuation.mem_maximalIdeal_iff (v := Valued.v)).mp hπ)
    (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot).ne'

-- The lift `K_v[X] ⧸ (q) → L_w` is compatible with the projections from `K[X] ⧸ (f)`.
private theorem lift_projFactor_map (hsq : Squarefree f) (a : AdjoinRoot f) :
    lift _ _ hq (projFactor (hsq.map_of_perfectField (algebraMap K (v.adicCompletion K))) q
        (AdjoinRoot.map (algebraMap K (v.adicCompletion K)) f _ dvd_rfl a)) =
      algebraMap _ (w.adicCompletion (AdjoinRoot (p : K[X]))) (projFactor hsq p a) := by
  obtain ⟨g, rfl⟩ := mk_surjective a
  rw [map_mk, projFactor_mk, lift_mk, projFactor_mk]
  exact eval₂_map_adicCompletionExtension p v w g

-- Divisibility of the order at the prime of the integral closure of `𝒪_v` in `K_v[X] ⧸ (q)`
-- below `𝒪_w` transports to `w`.
private theorem dvd_toAdd_valuationOfNeZero_of_lift (hsq : Squarefree f) {n : ℕ}
    (u : (AdjoinRoot f)ˣ)
    (h : (n : ℤ) ∣ Multiplicative.toAdd ((comapOfNeBot (integralClosureLift q hq) _
      (comap_integralClosureLift_ne_bot q hq)).valuationOfNeZero
        (Units.map (projFactor (hsq.map_of_perfectField (algebraMap K (v.adicCompletion K)))
          q).toMonoidHom (Units.map (AdjoinRoot.map (algebraMap K (v.adicCompletion K)) f _
            dvd_rfl).toMonoidHom u)))) :
    (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
      (Units.map (projFactor hsq p).toMonoidHom u)) := by
  rw [← valuationOfNeZero_maximalIdeal_adicCompletionIntegers]
  have hc : (algebraMap (w.adicCompletionIntegers (AdjoinRoot (p : K[X]))) _).comp
      (integralClosureLift q hq) = (lift _ _ hq).comp (algebraMap _ _) := RingHom.ext fun _ ↦ rfl
  have hu : ((Units.map (algebraMap _ (w.adicCompletion (AdjoinRoot (p : K[X])))).toMonoidHom
      (Units.map (projFactor hsq p).toMonoidHom u) : (w.adicCompletion (AdjoinRoot (p : K[X])))ˣ) :
        w.adicCompletion (AdjoinRoot (p : K[X]))) = lift _ _ hq
      (Units.map (projFactor (hsq.map_of_perfectField (algebraMap K (v.adicCompletion K)))
          q).toMonoidHom (Units.map (AdjoinRoot.map (algebraMap K (v.adicCompletion K)) f _
            dvd_rfl).toMonoidHom u) : AdjoinRoot (q : (v.adicCompletion K)[X])) :=
    (lift_projFactor_map q hq hsq u).symm
  exact dvd_toAdd_valuationOfNeZero_map hc (comap_integralClosureLift_ne_bot q hq) hu h

end Factor

-- The local condition at `v` gives the divisibility at a prime `w` above `v`: with `q` the factor
-- of `f` over `K_v` vanishing at the image of the root of `p` in `L_w`, apply the local condition
-- at the prime of the integral closure of `𝒪_v` in `K_v[X] ⧸ (q)` below `𝒪_w`.
private theorem dvd_toAdd_valuationOfNeZero_of_mem_selmerGroup (hsq : Squarefree f) {n : ℕ}
    (u : (AdjoinRoot f)ˣ)
    (h : (Units.map (AdjoinRoot.map (algebraMap K (v.adicCompletion K)) f _ dvd_rfl).toMonoidHom u :
      Units.ModPow (AdjoinRoot (f.map (algebraMap K (v.adicCompletion K)))) n) ∈
        selmerGroup (R := v.adicCompletionIntegers K) (hsq.map_of_perfectField _) ∅ n) :
    (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
      (Units.map (projFactor hsq p).toMonoidHom u)) := by
  obtain ⟨q, hq⟩ := Factors.exists_eval₂_eq_zero (map_ne_zero hsq.ne_zero)
    (eval₂_map_adicCompletionExtension_eq_zero p v w)
  exact dvd_toAdd_valuationOfNeZero_of_lift q hq hsq u
    ((mk_mem_selmerGroup_iff _ ∅ n _).mp h q _ fun ⟨_, h, _⟩ ↦ h)

end Completion

/-- **Local to global** for `AdjoinRoot.selmerGroup`: a class of `(K[X] ⧸ (f))ˣ` modulo `n`-th
powers lies in `A(S, n)` if its image over the completion `K_v` is unramified at every prime
`v ∉ S`. A prime `w` above `v` of a field factor `L = K[X] ⧸ (p)` gives the factor `q` of `f` over
`K_v` that vanishes at the image of the root of `p` in the completion `L_w`, and the order at `w`
is a multiple of the order at the prime of `K_v[X] ⧸ (q)` below `𝒪_w`. -/
theorem mem_selmerGroup_of_forall_adicCompletion (hsq : Squarefree f)
    {S : Set (HeightOneSpectrum R)} {n : ℕ} {x : Units.ModPow (AdjoinRoot f) n}
    (hx : ∀ v ∉ S, Units.ModPow.map (AdjoinRoot.map (algebraMap K (v.adicCompletion K)) f
        (f.map (algebraMap K (v.adicCompletion K))) dvd_rfl) n x ∈
      selmerGroup (R := v.adicCompletionIntegers K)
        (hsq.map_of_perfectField (algebraMap K (v.adicCompletion K))) ∅ n) :
    x ∈ selmerGroup hsq S n := by
  induction x using QuotientGroup.induction_on with | H u => ?_
  exact (mk_mem_selmerGroup_iff hsq S n u).mpr fun p w hw ↦
    dvd_toAdd_valuationOfNeZero_of_mem_selmerGroup p (w.under R) w hsq u
      (hx _ ((HeightOneSpectrum.mem_primesAbove_iff ..).not.mp hw))

end AdjoinRoot
