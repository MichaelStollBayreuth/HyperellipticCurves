/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Substitution of multivariate power series: continuity, constant coefficients, ring maps

The prime in `MvPowerSeries.continuous_subst'` distinguishes it from Mathlib's
`MvPowerSeries.continuous_subst`, which assumes the discrete uniformity on the coefficients,
whereas here they may carry any ring topology.

## Main definitions

* `MvPowerSeries.substRingHom`: substitution as a ring homomorphism, for use where a plain ring
  homomorphism is wanted — in particular between series over *different* variable types.

## Main statements

* `MvPowerSeries.continuous_subst'`: substitution is continuous for the product topologies, for
  any topological ring of coefficients.
* `MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero`: substituting a family without
  constant terms preserves the constant coefficient (Mathlib's
  `MvPowerSeries.constantCoeff_subst_eq_zero` only kills it, at the price of a hypothesis on the
  series substituted into).
* `MvPowerSeries.hasSubst_map_of_constantCoeff_zero`, `MvPowerSeries.map_substRingHom`: base
  change of a substitutable family, and its compatibility with substitution.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Filter Topology
open scoped MvPowerSeries.WithPiTopology

namespace MvPowerSeries

section subst

variable {σ R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Substitution of power series is continuous, coefficientwise: each coefficient of
`subst a f` is a fixed finite linear combination of coefficients of `f`.
This generalizes `MvPowerSeries.continuous_subst` from discrete coefficients to any
topological ring of coefficients. -/
theorem continuous_subst' {τ : Type*} {a : τ → MvPowerSeries σ R}
    (ha : MvPowerSeries.HasSubst a) :
    Continuous (MvPowerSeries.subst a : MvPowerSeries τ R → MvPowerSeries σ R) := by
  classical
  have hc (e : σ →₀ ℕ) : (Function.support fun d : τ →₀ ℕ ↦
      MvPowerSeries.coeff e (d.prod fun s i ↦ (a s) ^ i)).Finite := by
    have h1 := MvPowerSeries.coeff_subst_finite ha
      ((fun _ ↦ 1) : MvPowerSeries τ R) e
    simpa [Function.HasFiniteSupport, show ∀ d, MvPowerSeries.coeff (R := R) d
      ((fun _ ↦ 1) : MvPowerSeries τ R) = 1 from fun d ↦ rfl] using h1
  refine continuous_pi fun e ↦ ?_
  change Continuous fun f : MvPowerSeries τ R ↦ MvPowerSeries.coeff e (MvPowerSeries.subst a f)
  have heq : (fun f : MvPowerSeries τ R ↦ MvPowerSeries.coeff e (MvPowerSeries.subst a f))
      = fun f ↦ ∑ d ∈ (hc e).toFinset,
          MvPowerSeries.coeff d f * MvPowerSeries.coeff e (d.prod fun s i ↦ (a s) ^ i) := by
    funext f
    rw [MvPowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset]
    · exact Finset.sum_congr rfl fun d _ ↦ smul_eq_mul _ _
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      exact fun h0 ↦ hd (by rw [h0, smul_zero])
  rw [heq]
  exact continuous_finsetSum _ fun d _ ↦
    (MvPowerSeries.WithPiTopology.continuous_coeff R d).mul continuous_const

end subst

variable {σ R : Type*} [CommRing R]

/-- Substitution along families with vanishing constant coefficients preserves the
constant coefficient. Unlike Mathlib's `MvPowerSeries.constantCoeff_subst_eq_zero`, no
hypothesis on `f`: the constant coefficient is preserved, not just killed. -/
theorem constantCoeff_subst_of_constantCoeff_zero {τ : Type*}
    {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    (ha' : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries τ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  classical
  rw [constantCoeff_subst ha, finsum_eq_single _ 0 ?_]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
    rw [Finsupp.prod, map_prod, smul_eq_mul,
      Finset.prod_eq_zero hs (by
        rw [map_pow, ha' s, zero_pow (Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.mp hs)).ne']), mul_zero]

section substitution

variable {τ : Type*} {a : τ → MvPowerSeries σ R}

/-- Base change of a family with vanishing constant coefficients is again substitutable. -/
theorem hasSubst_map_of_constantCoeff_zero {S : Type*} [CommRing S] [Finite τ] (φ : R →+* S)
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst fun s ↦ map φ (a s) :=
  hasSubst_of_constantCoeff_zero fun s ↦ by rw [constantCoeff_map, ha s, map_zero]

/-- Substitution of a substitutable family of power series, as a ring homomorphism. Same
underlying function as `MvPowerSeries.substAlgHom`, but usable where a plain ring
homomorphism is wanted (in particular between series over *different* variable types with no
algebra structure relating them). -/
noncomputable def substRingHom (ha : HasSubst a) :
    MvPowerSeries τ R →+* MvPowerSeries σ R :=
  (substAlgHom ha).toRingHom

theorem substRingHom_apply (ha : HasSubst a) (f : MvPowerSeries τ R) :
    substRingHom ha f = subst a f :=
  substAlgHom_apply ha f

@[simp]
theorem substRingHom_X (ha : HasSubst a) (s : τ) : substRingHom ha (X s) = a s := by
  rw [substRingHom_apply, subst_X ha]

theorem substRingHom_comp_C (ha : HasSubst a) :
    (substRingHom ha).comp (C : R →+* MvPowerSeries τ R) = C :=
  RingHom.ext fun r ↦ by rw [RingHom.comp_apply, substRingHom_apply, subst_C]

theorem constantCoeff_substRingHom (ha : HasSubst a) (ha' : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries τ R) : constantCoeff (substRingHom ha f) = constantCoeff f := by
  rw [substRingHom_apply, constantCoeff_subst_of_constantCoeff_zero ha ha']

/-- Base change commutes with substitution. -/
theorem map_substRingHom {S : Type*} [CommRing S] (φ : R →+* S) (ha : HasSubst a)
    (haφ : HasSubst fun s ↦ map φ (a s)) (f : MvPowerSeries τ R) :
    map φ (substRingHom ha f) = substRingHom haφ (map φ f) := by
  rw [substRingHom_apply, substRingHom_apply, map_subst ha]

end substitution

end MvPowerSeries

end
