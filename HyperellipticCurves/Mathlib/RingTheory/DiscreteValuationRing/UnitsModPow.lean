/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Mathlib.GroupTheory.QuotientGroup.UnitsModPow
public import HyperellipticCurves.Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian

import HyperellipticCurves.Mathlib.Algebra.Group.Prod
import HyperellipticCurves.Mathlib.RingTheory.Henselian

/-!
# Units modulo powers of discrete valuation rings and of their fraction fields

For a discrete valuation ring `R` with fraction field `K` and a uniformizer `ϖ`, the units of `K`
modulo `n`-th powers are `ℤ/n × Rˣ/(Rˣ)ⁿ`. If `R` is moreover Henselian and `2` is a unit of `R`,
the units of `R` modulo squares are the units of the residue field `k` modulo squares, so that
`Kˣ/(Kˣ)² ≅ ℤ/2 × kˣ/(kˣ)²`; this covers `ℚ_[p]` for odd `p`.

## Main definitions

* `IsDiscreteValuationRing.modPowEquiv`: `Kˣ/(Kˣ)ⁿ ≃* ℤ/n × Rˣ/(Rˣ)ⁿ`, by `ϖ ^ m * u ↦ (m, u)`.
* `HenselianLocalRing.modPowTwoEquiv`: `Rˣ/(Rˣ)² ≃* kˣ/(kˣ)²` for a Henselian local ring `R` with
  residue field `k`, in which `2` is a unit.
* `IsDiscreteValuationRing.modPowTwoEquiv`: `Kˣ/(Kˣ)² ≃* ℤ/2 × kˣ/(kˣ)²` for a Henselian discrete
  valuation ring in which `2` is a unit.
-/

@[expose] public section

open IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type*) [Field K]
  [Algebra R K] [IsFractionRing R K] {ϖ : R}

-- The multiples of `n` in `ℤ`, written multiplicatively, are the kernel of the reduction
-- modulo `n`.
private lemma range_powMonoidHom_eq_ker (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range =
      (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).ker := by
  ext m
  obtain ⟨k, rfl⟩ : ∃ k, Multiplicative.ofAdd k = m := ⟨m.toAdd, rfl⟩
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_def, eq_comm, ← ofAdd_nsmul]

/-- The units of the fraction field `K` of a discrete valuation ring `R` modulo `n`-th powers are
`ℤ/n × Rˣ/(Rˣ)ⁿ`, by `ϖ ^ m * u ↦ (m mod n, u)` for a uniformizer `ϖ`
(`IsDiscreteValuationRing.unitsEquivProd`). -/
noncomputable def modPowEquiv (hϖ : Irreducible ϖ) (n : ℕ) :
    Units.ModPow K n ≃* Multiplicative (ZMod n) × Units.ModPow R n :=
  QuotientGroup.liftEquiv _ (φ := ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).prodMap
      (QuotientGroup.mk' _)).comp (unitsEquivProd K hϖ).toMonoidHom)
    (((ZMod.intCast_surjective (n := n)).prodMap (QuotientGroup.mk'_surjective _)).comp
      (unitsEquivProd K hϖ).surjective) <| by
    rw [← MonoidHom.comap_ker, MonoidHom.ker_prodMap, QuotientGroup.ker_mk',
      ← range_powMonoidHom_eq_ker, ← MonoidHom.range_prodMap,
      ← (unitsEquivProd K hϖ).symm.map_range_powMonoidHom, Subgroup.map_equiv_eq_comap_symm,
      MulEquiv.symm_symm]
    rfl

variable {K} in
theorem modPowEquiv_mk_of_val_eq (hϖ : Irreducible ϖ) (n : ℕ) {x : Kˣ} {m : ℤ} {u : Rˣ}
    (hx : (x : K) = algebraMap R K ϖ ^ m * algebraMap R K u) :
    modPowEquiv K hϖ n x = (.ofAdd (m : ZMod n), (u : Units.ModPow R n)) := by
  simp [modPowEquiv, unitsEquivProd_apply_of_val_eq hϖ hx]

end IsDiscreteValuationRing

namespace HenselianLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- In a Henselian local ring `R` in which `2` is a unit, the units modulo squares are the units
of the residue field modulo squares (`HenselianLocalRing.isSquare_iff_isSquare_residue`). -/
noncomputable def modPowTwoEquiv (h2 : IsUnit (2 : R)) :
    Units.ModPow R 2 ≃* Units.ModPow (ResidueField R) 2 :=
  QuotientGroup.liftEquiv _ (φ := (QuotientGroup.mk' _).comp (Units.map (residue R).toMonoidHom))
    ((QuotientGroup.mk'_surjective _).comp
      (surjective_units_map_of_local_ringHom _ residue_surjective inferInstance)) <| by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.eq_one_iff, Units.ModPow.mk_eq_one_iff_isSquare,
      Units.ModPow.mk_eq_one_iff_isSquare, Units.coe_map, isSquare_iff_isSquare_residue h2 u.isUnit]
    rfl

@[simp]
theorem modPowTwoEquiv_mk (h2 : IsUnit (2 : R)) (u : Rˣ) :
    modPowTwoEquiv h2 u = (Units.map (residue R).toMonoidHom u : Units.ModPow (ResidueField R) 2) :=
  rfl

end HenselianLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}

/-- **Square classes of a Henselian discrete valuation ring** with `2` a unit, such as `ℚ_[p]`
for odd `p`: by `ϖ ^ n * u ↦ (n mod 2, ū)`, `Kˣ/(Kˣ)²` is `ℤ/2 × kˣ/(kˣ)²` for the residue
field `k`. -/
noncomputable def modPowTwoEquiv (h2 : IsUnit (2 : R)) (hϖ : Irreducible ϖ) :
    Units.ModPow K 2 ≃* Multiplicative (ZMod 2) × Units.ModPow (ResidueField R) 2 :=
  (modPowEquiv K hϖ 2).trans ((MulEquiv.refl _).prodCongr (HenselianLocalRing.modPowTwoEquiv h2))

variable {K} in
theorem modPowTwoEquiv_mk_of_val_eq (h2 : IsUnit (2 : R)) (hϖ : Irreducible ϖ) {x : Kˣ} {m : ℤ}
    {u : Rˣ} (hx : (x : K) = algebraMap R K ϖ ^ m * algebraMap R K u) :
    modPowTwoEquiv K h2 hϖ x = (.ofAdd (m : ZMod 2),
      (Units.map (residue R).toMonoidHom u : Units.ModPow (ResidueField R) 2)) := by
  simp [modPowTwoEquiv, modPowEquiv_mk_of_val_eq hϖ 2 hx]

end IsDiscreteValuationRing

end
