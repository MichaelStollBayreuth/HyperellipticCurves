/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.JacobianStructure
public import HyperellipticCurves.Descent.Local
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

import HyperellipticCurves.Archive.BaseChangeInjectivity
import HyperellipticCurves.Curve.MumfordReduction
import HyperellipticCurves.Descent.Image
import HyperellipticCurves.Descent.Kernel
import HyperellipticCurves.Mathlib.Algebra.BigOperators.Group.Finset.Basic
import HyperellipticCurves.Mathlib.Algebra.Group.Subgroup.Finite
import HyperellipticCurves.Mathlib.Algebra.Group.Subgroup.Ker
import HyperellipticCurves.Mathlib.Algebra.Polynomial.Coeff
import HyperellipticCurves.Mathlib.Algebra.Polynomial.FieldDivision
import HyperellipticCurves.Mathlib.GroupTheory.Torsion
import HyperellipticCurves.Mathlib.NumberTheory.Padics.HeightOneSpectrum
import HyperellipticCurves.Mathlib.NumberTheory.Padics.Hensel
import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.ChineseRemainder
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Resultant.Basic
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.ReduceModChar

/-!
# Example E1: `y ^ 2 = x (x ^ 2 - 1) (x ^ 2 - 9)`

The curve `C : y ^ 2 = f(x)` with `f = x ^ 5 - 10 x ^ 3 + 9 x`, of genus `2`, whose roots
`α = -3, -1, 0, 1, 3` are rational (blueprint `rem:ds-e1` to `thm:ds-e1`). Under the cited inputs
(Loc) for `ℚ_[2]` and `ℚ_[3]` (`ChabautyColeman.HypJac.LocalStructure`) and (Red) for `p = 5`
(`ChabautyColeman.HypJac.TorsionReduction`), `2`-descent with the local conditions at `ℚ_[2]` and
`ℚ_[3]` and reduction modulo `5` give `J(ℚ) = J(ℚ)[2]`, of order `16`, and
`C(ℚ) = {∞, (0, 0), (± 1, 0), (± 3, 0)}`; the Mordell-Weil theorem is not used.

## Main definitions

* `ChabautyColeman.DescentExample1.f`, `ChabautyColeman.DescentExample1.F`: the polynomial over `ℚ`
  and over `ℤ`.
* `ChabautyColeman.DescentExample1.α`: its roots.
* `ChabautyColeman.DescentExample1.S`: the primes `2` and `3` of `ℤ`.

## Main statements

* `ChabautyColeman.DescentExample1.range_descentMap_three`,
  `ChabautyColeman.DescentExample1.range_descentMap_two`: the images of the `x - T` map over `ℚ_[3]`
  and `ℚ_[2]`, of orders `16` and `64` (blueprint `lem:ds-e1-local`).
* `ChabautyColeman.DescentExample1.relaxedSelmerGroup_eq`: the relaxed Selmer group for `{2, 3}` and
  the local conditions at `ℚ_[2]` and `ℚ_[3]` is the image of `J(ℚ)[2]` (blueprint
  `prop:ds-e1-sel`).
* `ChabautyColeman.DescentExample1.exponent_hypJac_zmod_five`: `J̃(𝔽₅)` has exponent `2` (blueprint
  `lem:ds-e1-five`).
* `ChabautyColeman.DescentExample1.ker_powMonoidHom_two_eq_top`,
  `ChabautyColeman.DescentExample1.card_hypJac`: `J(ℚ) = J(ℚ)[2]`, of order `16` (blueprint
  `thm:ds-e1`).
* `ChabautyColeman.DescentExample1.ratPoints_eq`: the affine rational points are the five points
  `(α, 0)` (blueprint `thm:ds-e1`).

## Implementation notes

The computations run in root coordinates: `L = ℚ[X] / (f)` and its analogues over `ℚ_[2]` and
`ℚ_[3]` are products of five copies of the base field (`AdjoinRoot.modPowEquivPiOfRoots`), and the
square classes of `ℚ_[2]` and `ℚ_[3]` are identified with the groups `ℤ/2 × (ℤ/8)ˣ` and
`ℤ/2 × (ℤ/3)ˣ` (`Padic.modPowTwoEquivZModEight`, `Padic.modPowTwoEquiv`), in which `decide`
computes. The classes that occur are products of the classes of `-1`, `2`, `3` with exponents
given by tables, except those of `4 - θ` and `1 / 5 - θ` over `ℚ_[2]`, which agree there with the
global classes with root coordinates `-1, -3, 1, 3, 1` and `-3, -2, -3, 3, -6`. The relations
among the finitely many values are checked by `decide`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman.DescentExample1

/-- The polynomial `x (x ^ 2 - 1) (x ^ 2 - 9)` of example E1 (blueprint `set:ds-e1`). -/
noncomputable def f : ℚ[X] := X ^ 5 - 10 * X ^ 3 + 9 * X

/-- The polynomial `ChabautyColeman.DescentExample1.f` with integer coefficients, for its reduction
modulo `5`. -/
noncomputable def F : ℤ[X] := X ^ 5 - 10 * X ^ 3 + 9 * X

/-- The roots `-3, -1, 0, 1, 3` of `ChabautyColeman.DescentExample1.f`. -/
def α : Fin 5 → ℤ := ![-3, -1, 0, 1, 3]

theorem map_F : F.map (Int.castRingHom ℚ) = f := by
  simp [F, f]

theorem natDegree_f : f.natDegree = 5 := by
  rw [f]
  compute_degree!

theorem F_eq_prod : F = ∏ i, (X - C (α i)) := by
  simp [F, Fin.prod_univ_five, α]
  ring

theorem natDegree_F : F.natDegree = 5 := by
  rw [F]
  compute_degree!

theorem monic_F : F.Monic := by
  rw [F]
  monicity!

/-- The discriminant of `ChabautyColeman.DescentExample1.F`, from the resultant of `F` and `F'`
(`Polynomial.resultant_deriv`), the product of the values `144, -16, 9, -16, 144` of `F'` at the
roots. -/
theorem discr_F : F.discr = 2 ^ 16 * 3 ^ 6 := by
  have hle : (derivative F).natDegree ≤ F.natDegree - 1 :=
    (natDegree_derivative_le F).trans (by rw [natDegree_F])
  have h := resultant_prod_left Finset.univ (fun i ↦ X - C (α i)) (derivative F) _
    (by rw [Finset.prod_eq_one fun i _ ↦ leadingCoeff_X_sub_C (α i)]; exact one_ne_zero) hle
  rw [← F_eq_prod, resultant_deriv (natDegree_pos_iff_degree_pos.mp (by simp [natDegree_F]))] at h
  simp only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hle] at h
  have hval : ∏ i, eval (α i) (derivative F) = 2 ^ 16 * 3 ^ 6 := by
    simp [F, Fin.prod_univ_five, α]
  rw [hval, natDegree_F, monic_F.leadingCoeff] at h
  simpa using h

theorem monic_f : f.Monic :=
  map_F ▸ monic_F.map _

theorem f_ne_zero : f ≠ 0 :=
  monic_f.ne_zero

section Field

variable {K : Type*} [Field K] [CharZero K]

theorem map_f_eq_prod : f.map (algebraMap ℚ K) = ∏ i, (X - C (α i : K)) := by
  simp [f, Fin.prod_univ_five, α]
  ring

theorem α_injective : Function.Injective fun i ↦ (α i : K) :=
  Int.cast_injective.comp (by decide : Function.Injective α)

variable {g : K[X]}

theorem isRoot_α (hg : f.map (algebraMap ℚ K) = g) (i : Fin 5) : g.IsRoot (α i) := by
  rw [← hg, map_f_eq_prod, IsRoot, eval_prod, Finset.prod_eq_zero_iff]
  exact ⟨i, Finset.mem_univ i, by simp⟩

theorem ne_zero_of_map_f_eq (hg : f.map (algebraMap ℚ K) = g) : g ≠ 0 :=
  hg ▸ (Polynomial.map_ne_zero_iff (algebraMap ℚ K).injective).mpr f_ne_zero

theorem natDegree_le_of_map_f_eq (hg : f.map (algebraMap ℚ K) = g) :
    g.natDegree ≤ Fintype.card (Fin 5) := by
  rw [← hg, natDegree_map, natDegree_f, Fintype.card_fin]

-- The root coordinates of `L^× / (L^×)^2`, `L = K[X] / (g)`, at the roots `α i`.
private noncomputable def rootCoords (hg : f.map (algebraMap ℚ K) = g) :
    Units.ModPow (AdjoinRoot g) 2 ≃* (Fin 5 → Units.ModPow K 2) :=
  AdjoinRoot.modPowEquivPiOfRoots (ne_zero_of_map_f_eq hg) α_injective (isRoot_α hg)
    (natDegree_le_of_map_f_eq hg) 2

-- The units `-1`, `2`, `3` of `K`, whose classes generate the classes of `ℚ(S, 2)`.
variable (K) in
private def baseUnit : Fin 3 → Kˣ :=
  ![-1, Units.mk0 2 two_ne_zero, Units.mk0 3 three_ne_zero]

-- The unit `(-1) ^ e 0 * 2 ^ e 1 * 3 ^ e 2` of `K`.
variable (K) in
private def expUnit (e : Fin 3 → ℕ) : Kˣ :=
  ∏ k, baseUnit K k ^ e k

-- The integer `(-1) ^ e 0 * 2 ^ e 1 * 3 ^ e 2`.
private def expInt (e : Fin 3 → ℕ) : ℤ :=
  ∏ k, ![-1, 2, 3] k ^ e k

private theorem coe_expUnit (e : Fin 3 → ℕ) : (expUnit K e : K) = expInt e := by
  simp [expUnit, expInt, baseUnit, Fin.prod_univ_three]

private theorem map_expUnit {H : Type*} [CommMonoid H] (ψ : Units.ModPow K 2 →* H)
    (e : Fin 3 → ℕ) : ψ (expUnit K e) = ∏ k, ψ (baseUnit K k) ^ e k := by
  simp [expUnit, QuotientGroup.mk_prod]

-- The exponents of `-1`, `2`, `3` of the root coordinates of the values of the `x - T` map at the
-- points `(α j, 0)`: `α j - α i` for `i ≠ j`, and `f'(α j)` for `i = j`.
private def torsionExp : Fin 5 → Fin 5 → Fin 3 → ℕ := ![
  ![![0, 4, 2], ![1, 1, 0], ![1, 0, 1], ![1, 2, 0], ![1, 1, 1]],
  ![![0, 1, 0], ![1, 4, 0], ![1, 0, 0], ![1, 1, 0], ![1, 2, 0]],
  ![![0, 0, 1], ![0, 0, 0], ![0, 0, 2], ![1, 0, 0], ![1, 0, 1]],
  ![![0, 2, 0], ![0, 1, 0], ![0, 0, 0], ![1, 4, 0], ![1, 1, 0]],
  ![![0, 1, 1], ![0, 2, 0], ![0, 0, 1], ![0, 1, 0], ![0, 4, 2]]]

private theorem expInt_torsionExp_of_ne {i j : Fin 5} (h : i ≠ j) :
    expInt (torsionExp j i) = α j - α i := by
  decide +revert

private theorem expInt_torsionExp_self (j : Fin 5) :
    expInt (torsionExp j j) = 5 * α j ^ 4 - 30 * α j ^ 2 + 9 := by
  decide +revert

variable [Fact (Odd g.natDegree)] [Fact (Squarefree g)]

-- The root coordinates of the values of the `x - T` map at the points `(α j, 0)`.
private theorem rootCoords_descentMap_mumfordClass (hg : f.map (algebraMap ℚ K) = g)
    (j i : Fin 5) :
    rootCoords hg (HypJac.descentMap g (mumfordClass g (X - C (α j : K)) 0)) i =
      expUnit K (torsionExp j i) := by
  rw [rootCoords, AdjoinRoot.modPowEquivPiOfRoots_apply]
  rcases eq_or_ne i j with rfl | hij
  · refine HypJac.map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero_self g (isRoot_α hg i) ?_
    subst hg
    rw [(monic_f.map _).leadingCoeff, one_mul]
    simp [coe_expUnit, expInt_torsionExp_self, f]
    ring
  · refine HypJac.map_liftAlgHom_descentMap_mumfordClass_X_sub_C_zero_of_ne g (isRoot_α hg j)
      (isRoot_α hg i) (α_injective.ne hij) ?_
    subst hg
    rw [(monic_f.map _).leadingCoeff, one_mul]
    simp [coe_expUnit, expInt_torsionExp_of_ne hij]

end Field

/-- The primes `2` and `3` of `ℤ`, at which `ChabautyColeman.DescentExample1.f` does not have
separable reduction. -/
noncomputable def S : Set (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  {Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩,
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩}

/-- `ChabautyColeman.DescentExample1.f` has separable reduction outside `2` and `3`: its
discriminant is `2 ^ 16 * 3 ^ 6` (`ChabautyColeman.DescentExample1.discr_F`). -/
theorem hasSeparableReduction_of_notMem {v : IsDedekindDomain.HeightOneSpectrum ℤ} (hv : v ∉ S) :
    f.HasSeparableReduction (v.valuation ℚ) where
  coeff_le_one i := by
    rw [← map_F, coeff_map]
    exact (v.valuation_of_algebraMap (F.coeff i)).trans_le (v.intValuation_le_one _)
  leadingCoeff_eq_one := by rw [monic_f.leadingCoeff, map_one]
  discr_eq_one := by
    rw [← map_F, discr_map_of_injective (RingHom.injective_int _), discr_F]
    refine (v.valuation_of_algebraMap _).trans (v.intValuation_eq_one_iff.mpr fun h ↦ ?_)
    rcases v.isPrime.mem_or_mem h with h | h
    · exact hv (.inl (Rat.HeightOneSpectrum.eq_primesEquiv_symm_of_natCast_mem Nat.prime_two
        (v.isPrime.mem_of_pow_mem 16 h)))
    · exact hv (.inr (Rat.HeightOneSpectrum.eq_primesEquiv_symm_of_natCast_mem Nat.prime_three
        (v.isPrime.mem_of_pow_mem 6 h)))

instance fact_odd_natDegree_f : Fact (Odd f.natDegree) :=
  ⟨natDegree_f ▸ by decide⟩

private theorem map_f_self : f.map (algebraMap ℚ ℚ) = f := by
  simp

instance fact_squarefree_f : Fact (Squarefree f) :=
  ⟨squarefree_of_injective f_ne_zero α_injective (isRoot_α map_f_self)
    (natDegree_le_of_map_f_eq map_f_self)⟩

/-! ### The square classes of `ℚ_[2]` and `ℚ_[3]` -/

private theorem range_powMonoidHom_two_le_ker :
    (powMonoidHom 2 : (ZMod 3)ˣ →* (ZMod 3)ˣ).range ≤ (MonoidHom.id (ZMod 3)ˣ).ker := by
  rintro _ ⟨u, rfl⟩
  decide +revert

-- The square classes of `ℚ_[3]` in a form that `decide` can compute with: `(ZMod 3)ˣ` has no
-- nontrivial squares.
private noncomputable def ψ₃ : Units.ModPow ℚ_[3] 2 →* Multiplicative (ZMod 2) × (ZMod 3)ˣ :=
  ((MonoidHom.id _).prodMap (QuotientGroup.lift (powMonoidHom 2 : (ZMod 3)ˣ →* (ZMod 3)ˣ).range
    (MonoidHom.id _) range_powMonoidHom_two_le_ker)).comp
      (Padic.modPowTwoEquiv 3 (by decide)).toMonoidHom

-- The unit `3` of `ZMod 8`.
private def three₈ : (ZMod 8)ˣ := ⟨3, 3, rfl, rfl⟩

-- The values of `Padic.modPowTwoEquivZModEight` at the classes of `-1`, `2`, `3`.
private def h₂ : Fin 3 → Multiplicative (ZMod 2) × (ZMod 8)ˣ :=
  ![(1, -1), (.ofAdd 1, 1), (1, three₈)]

-- The values of `ψ₃` at the classes of `-1`, `2`, `3`.
private def h₃ : Fin 3 → Multiplicative (ZMod 2) × (ZMod 3)ˣ :=
  ![(1, -1), (1, -1), (.ofAdd 1, 1)]

private theorem modPowTwoEquivZModEight_baseUnit (k : Fin 3) :
    Padic.modPowTwoEquivZModEight (baseUnit ℚ_[2] k) = h₂ k := by
  fin_cases k
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 0 (-1) (-1) (by simp [baseUnit]) (by simp)]
    rfl
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 1 1 1 (by simp [baseUnit]) (by simp)]
    rfl
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 0 3 three₈ (by simp [baseUnit]) (by decide)]
    rfl

private theorem ψ₃_baseUnit (k : Fin 3) : ψ₃ (baseUnit ℚ_[3] k) = h₃ k := by
  rw [ψ₃, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  fin_cases k
  · rw [Padic.modPowTwoEquiv_mk_of_val_eq _ 0 (-1) (-1) (by simp [baseUnit]) (by simp)]
    rfl
  · rw [Padic.modPowTwoEquiv_mk_of_val_eq _ 0 2 (-1) (by simp [baseUnit]) (by decide)]
    rfl
  · rw [Padic.modPowTwoEquiv_mk_of_val_eq _ 1 1 1 (by simp [baseUnit]) (by simp)]
    rfl

-- The unit `5` of `ZMod 8`.
private def five₈ : (ZMod 8)ˣ := ⟨5, 5, rfl, rfl⟩

-- `Padic.modPowTwoEquivZModEight_mk_of_val_eq` up to a square factor `d ^ 2`.
private theorem modPowTwoEquivZModEight_mk_of_mul_sq_eq {x d : ℚ_[2]ˣ} (n : ℕ) (m : ℤ)
    (w : (ZMod 8)ˣ) (hx : (x : ℚ_[2]) * d ^ 2 = 2 ^ n * m) (hw : (w : ZMod 8) = m) :
    Padic.modPowTwoEquivZModEight x = (.ofAdd (n : ZMod 2), w) := by
  rw [← QuotientGroup.mk_mul_of_mem (s := (powMonoidHom 2 : ℚ_[2]ˣ →* ℚ_[2]ˣ).range) x ⟨d, rfl⟩,
    Padic.modPowTwoEquivZModEight_mk_of_val_eq n m w (by simpa using hx) hw]

-- The exponents of `-1`, `2`, `3` of the root coordinates of a global class `P` that agrees with
-- the class of `4 - θ` over `ℚ_[2]`: `-1, -3, 1, 3, 1`.
private def pExp : Fin 5 → Fin 3 → ℕ :=
  ![![1, 0, 0], ![1, 0, 1], ![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]

-- The exponents of `-1`, `2`, `3` of the root coordinates of a global class `Q` that agrees with
-- the class of `1 / 5 - θ` over `ℚ_[2]`: `-3, -2, -3, 3, -6`.
private def qExp : Fin 5 → Fin 3 → ℕ :=
  ![![1, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 0, 1], ![1, 1, 1]]

private theorem modPowTwoEquivZModEight_four_sub (i : Fin 5) {v : ℚ_[2]ˣ}
    (hv : (v : ℚ_[2]) = 4 - α i) :
    Padic.modPowTwoEquivZModEight v = ∏ k, h₂ k ^ pExp i k := by
  fin_cases i
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 0 7 (-1) (by norm_num [hv, α]) (by decide)]
    decide
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 0 5 five₈ (by norm_num [hv, α]) (by decide)]
    decide
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 2 1 1 (by norm_num [hv, α]) (by decide)]
    decide
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 0 3 three₈ (by norm_num [hv, α]) (by decide)]
    decide
  · rw [Padic.modPowTwoEquivZModEight_mk_of_val_eq 0 1 1 (by norm_num [hv, α]) (by decide)]
    decide

private theorem modPowTwoEquivZModEight_inv_five_sub (i : Fin 5) {v : ℚ_[2]ˣ}
    (hv : (v : ℚ_[2]) = 5⁻¹ - α i) :
    Padic.modPowTwoEquivZModEight v = ∏ k, h₂ k ^ qExp i k := by
  have h5 : (5 : ℚ_[2]) ≠ 0 := by norm_num
  fin_cases i
  · rw [modPowTwoEquivZModEight_mk_of_mul_sq_eq (d := .mk0 5 h5) 4 5 five₈
      (by norm_num [hv, α]) (by decide)]
    decide
  · rw [modPowTwoEquivZModEight_mk_of_mul_sq_eq (d := .mk0 5 h5) 1 15 (-1)
      (by norm_num [hv, α]) (by decide)]
    decide
  · rw [modPowTwoEquivZModEight_mk_of_mul_sq_eq (d := .mk0 5 h5) 0 5 five₈
      (by norm_num [hv, α]) (by decide)]
    decide
  · rw [modPowTwoEquivZModEight_mk_of_mul_sq_eq (d := .mk0 5 h5) 2 (-5) three₈
      (by norm_num [hv, α]) (by decide)]
    decide
  · rw [modPowTwoEquivZModEight_mk_of_mul_sq_eq (d := .mk0 5 h5) 1 (-35) five₈
      (by norm_num [hv, α]) (by decide)]
    decide

/-! ### Local coordinates -/

section Coords

variable {K : Type*} [Field K] [CharZero K] {g : K[X]} {H : Type*} [CommMonoid H]

-- The root coordinates followed by a homomorphism `ψ` on `K^× / (K^×)^2`.
private noncomputable def coords (hg : f.map (algebraMap ℚ K) = g)
    (ψ : Units.ModPow K 2 →* H) : Units.ModPow (AdjoinRoot g) 2 →* (Fin 5 → H) :=
  (MonoidHom.compLeft ψ (Fin 5)).comp (rootCoords hg).toMonoidHom

private theorem coords_apply (hg : f.map (algebraMap ℚ K) = g) (ψ : Units.ModPow K 2 →* H)
    (x : Units.ModPow (AdjoinRoot g) 2) (i : Fin 5) : coords hg ψ x i = ψ (rootCoords hg x i) :=
  rfl

private theorem finite_modPow_adjoinRoot (hg : f.map (algebraMap ℚ K) = g)
    [Finite (Units.ModPow K 2)] : Finite (Units.ModPow (AdjoinRoot g) 2) :=
  .of_equiv _ (rootCoords hg).symm.toEquiv

-- The class of `x₀ - θ` has root coordinates the classes of `x₀ - α i`.
private theorem exists_rootCoords_eq_of_coe_eq (hg : f.map (algebraMap ℚ K) = g) {x₀ : K}
    {u : (AdjoinRoot g)ˣ} (hu : (u : AdjoinRoot g) = AdjoinRoot.of g x₀ - AdjoinRoot.root g)
    (i : Fin 5) : ∃ v : Kˣ, (v : K) = x₀ - α i ∧ rootCoords hg u i = v := by
  refine ⟨_, ?_, by rw [rootCoords, AdjoinRoot.modPowEquivPiOfRoots_apply, Units.ModPow.map_mk]⟩
  simp [hu]

variable [Fact (Odd g.natDegree)] [Fact (Squarefree g)]

private theorem coords_descentMap_mumfordClass (hg : f.map (algebraMap ℚ K) = g)
    {ψ : Units.ModPow K 2 →* H} {h : Fin 3 → H} (hψ : ∀ k, ψ (baseUnit K k) = h k) (j : Fin 5) :
    coords hg ψ (HypJac.descentMap g (mumfordClass g (X - C (α j : K)) 0)) =
      fun i ↦ ∏ k, h k ^ torsionExp j i k := by
  funext i
  rw [coords_apply, rootCoords_descentMap_mumfordClass, map_expUnit]
  simp only [hψ]

end Coords

-- The vector of products `∏ k, h k ^ e i k`.
private def expVec {H : Type*} [CommMonoid H] (h : Fin 3 → H) (e : Fin 5 → Fin 3 → ℕ) :
    Fin 5 → H :=
  fun i ↦ ∏ k, h k ^ e i k

/-! ### The local images (blueprint `lem:ds-e1-local`) -/

private theorem card_ker_powMonoidHom_two_of_map_f_eq {K : Type*} [Field K] [CharZero K]
    {g : K[X]} [Fact (Odd g.natDegree)] [Fact (Squarefree g)] (hg : f.map (algebraMap ℚ K) = g) :
    Nat.card (powMonoidHom 2 : HypJac K g →* HypJac K g).ker = 16 := by
  rw [HypJac.card_ker_powMonoidHom_two, Factors.card_eq_of_injective (ne_zero_of_map_f_eq hg)
    α_injective (isRoot_α hg) (natDegree_le_of_map_f_eq hg)]
  rfl

private theorem eq_empty_of_prod_eq_one_three (s : Finset (Fin 4))
    (h : ∏ j ∈ s, expVec h₃ (torsionExp j.castSucc) = 1) : s = ∅ := by
  decide +kernel +revert

private theorem eq_empty_of_prod_eq_one_two (s : Finset (Fin 4 ⊕ Fin 2))
    (h : ∏ j ∈ s, Sum.elim (fun j ↦ expVec h₂ (torsionExp j.castSucc))
      ![expVec h₂ pExp, expVec h₂ qExp] j = 1) : s = ∅ := by
  decide +kernel +revert

/-- **The image of the `x - T` map over `ℚ_[3]`** (blueprint `lem:ds-e1-local`): under (Loc) for
`ℚ_[3]`, it is generated by the images of the five points `(α j, 0)`, a group of order `16`. -/
theorem range_descentMap_three
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2) :
    (HypJac.descentMap (f.map (algebraMap ℚ ℚ_[3]))).range =
      Subgroup.closure (Set.range fun j ↦ HypJac.descentMap (f.map (algebraMap ℚ ℚ_[3]))
        (mumfordClass _ (X - C (α j : ℚ_[3])) 0)) := by
  have := finite_modPow_adjoinRoot (K := ℚ_[3]) rfl
  refine L₃.range_descentMap_eq_of_le_of_card_ge (by decide) ((Subgroup.closure_le _).mpr
    (Set.range_subset_iff.mpr fun j ↦ MonoidHom.mem_range.mpr ⟨_, rfl⟩)) ?_
  rw [card_ker_powMonoidHom_two_of_map_f_eq rfl]
  refine (Subgroup.card_closure_range_eq_two_pow_of_monoidHom (ι := Fin 4)
    (fun _ ↦ Units.ModPow.pow_eq_one _) (coords rfl ψ₃)
    fun s hs ↦ eq_empty_of_prod_eq_one_three s ?_).ge.trans
      (Subgroup.card_le_of_le (Subgroup.closure_mono (Set.range_comp_subset_range Fin.castSucc _)))
  simp only [Function.comp_apply, coords_descentMap_mumfordClass rfl ψ₃_baseUnit] at hs
  exact hs

private theorem coords_four {u : (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2])))ˣ}
    (hu : (u : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) = AdjoinRoot.of _ 4 - AdjoinRoot.root _) :
    coords rfl Padic.modPowTwoEquivZModEight.toMonoidHom u = expVec h₂ pExp := by
  funext i
  obtain ⟨w, hw, h⟩ := exists_rootCoords_eq_of_coe_eq rfl hu i
  rw [coords_apply, h]
  exact modPowTwoEquivZModEight_four_sub i hw

private theorem coords_inv_five {u : (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2])))ˣ}
    (hu : (u : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) = AdjoinRoot.of _ 5⁻¹ - AdjoinRoot.root _) :
    coords rfl Padic.modPowTwoEquivZModEight.toMonoidHom u = expVec h₂ qExp := by
  funext i
  obtain ⟨w, hw, h⟩ := exists_rootCoords_eq_of_coe_eq rfl hu i
  rw [coords_apply, h]
  exact modPowTwoEquivZModEight_inv_five_sub i hw

private theorem eval_four : (f.map (algebraMap ℚ ℚ_[2])).eval 4 = 420 := by
  norm_num [f]

private theorem eval_inv_five : (f.map (algebraMap ℚ ℚ_[2])).eval 5⁻¹ = 5376 / 3125 := by
  norm_num [f]

private theorem isSquare_eval_four : IsSquare ((f.map (algebraMap ℚ ℚ_[2])).eval 4) := by
  rw [eval_four, ← Units.val_mk0 (show (420 : ℚ_[2]) ≠ 0 by norm_num),
    ← Units.ModPow.mk_eq_one_iff_isSquare,
    ← map_eq_one_iff _ Padic.modPowTwoEquivZModEight.injective,
    Padic.modPowTwoEquivZModEight_mk_of_val_eq 2 105 1 (by norm_num) (by decide)]
  decide

private theorem isSquare_eval_inv_five : IsSquare ((f.map (algebraMap ℚ ℚ_[2])).eval 5⁻¹) := by
  rw [eval_inv_five, ← Units.val_mk0 (show (5376 / 3125 : ℚ_[2]) ≠ 0 by norm_num),
    ← Units.ModPow.mk_eq_one_iff_isSquare,
    ← map_eq_one_iff _ Padic.modPowTwoEquivZModEight.injective,
    modPowTwoEquivZModEight_mk_of_mul_sq_eq (d := .mk0 125 (by norm_num)) 8 105 1 (by norm_num)
      (by decide)]
  decide

-- The lower bound `64` for the order of the subgroup generated by the values at the points
-- `(α j, 0)` and the classes of `4 - θ` and `1 / 5 - θ` over `ℚ_[2]`.
private theorem le_card_closure_two {u v : (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2])))ˣ}
    (hu : (u : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) = AdjoinRoot.of _ 4 - AdjoinRoot.root _)
    (hv : (v : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) = AdjoinRoot.of _ 5⁻¹ - AdjoinRoot.root _) :
    2 ^ (2 * 1) * 16 ≤ Nat.card (Subgroup.closure (Set.range (fun j ↦
      HypJac.descentMap (f.map (algebraMap ℚ ℚ_[2])) (mumfordClass _ (X - C (α j : ℚ_[2])) 0)) ∪
        {(u : Units.ModPow _ 2), (v : Units.ModPow _ 2)})) := by
  have := finite_modPow_adjoinRoot (K := ℚ_[2]) rfl
  refine (Subgroup.card_closure_range_eq_two_pow_of_monoidHom (ι := Fin 4 ⊕ Fin 2)
    (fun _ ↦ Units.ModPow.pow_eq_one _) (coords rfl Padic.modPowTwoEquivZModEight.toMonoidHom)
    fun s hs ↦ eq_empty_of_prod_eq_one_two s ?_).ge.trans (Subgroup.card_le_of_le
      (Subgroup.closure_mono (Set.Sum.elim_range _
        ![(u : Units.ModPow (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) 2), v] ▸
        Set.union_subset_union (Set.range_comp_subset_range Fin.castSucc _)
          (Matrix.range_cons_cons_empty _ _ _).subset)))
  rwa [Finset.prod_congr rfl fun j _ ↦ ?_] at hs
  rcases j with j | j
  · exact coords_descentMap_mumfordClass rfl modPowTwoEquivZModEight_baseUnit j.castSucc
  · fin_cases j
    exacts [coords_four hu, coords_inv_five hv]

/-- **The image of the `x - T` map over `ℚ_[2]`** (blueprint `lem:ds-e1-local`): under (Loc) for
`ℚ_[2]`, it is generated by the images of the five points `(α j, 0)` and the classes of `4 - θ` and
`1 / 5 - θ`, the images of the points of `C(ℚ_[2])` with `x = 4` and `x = 1 / 5`, a group of order
`64`. -/
theorem range_descentMap_two
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    {u v : (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2])))ˣ}
    (hu : (u : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) = AdjoinRoot.of _ 4 - AdjoinRoot.root _)
    (hv : (v : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) = AdjoinRoot.of _ 5⁻¹ - AdjoinRoot.root _) :
    (HypJac.descentMap (f.map (algebraMap ℚ ℚ_[2]))).range =
      Subgroup.closure (Set.range (fun j ↦ HypJac.descentMap (f.map (algebraMap ℚ ℚ_[2]))
        (mumfordClass _ (X - C (α j : ℚ_[2])) 0)) ∪
          {(u : Units.ModPow _ 2), (v : Units.ModPow _ 2)}) := by
  have := finite_modPow_adjoinRoot (K := ℚ_[2]) rfl
  refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le _).mpr (Set.union_subset
    (Set.range_subset_iff.mpr fun j ↦ MonoidHom.mem_range.mpr ⟨_, rfl⟩) (Set.pair_subset
      (HypJac.mk_mem_range_descentMap_of_isSquare (monic_f.map _) isSquare_eval_four hu)
      (HypJac.mk_mem_range_descentMap_of_isSquare (monic_f.map _) isSquare_eval_inv_five hv))))
    ?_).symm
  rw [HypJac.card_range_descentMap_eq_card_quotient, L₂.card_modPow_two,
    card_ker_powMonoidHom_two_of_map_f_eq rfl, Module.finrank_self]
  exact le_card_closure_two hu hv

/-! ### The relaxed Selmer group (blueprint `prop:ds-e1-sel`) -/

instance fact_prime_two_three (i : Fin 2) : Fact (Nat.Prime (![2, 3] i)) :=
  ⟨by fin_cases i; exacts [Nat.prime_two, Nat.prime_three]⟩

-- The root coordinates commute with base change.
private theorem rootCoords_map (K : Type*) [Field K] [CharZero K]
    (x : Units.ModPow (AdjoinRoot f) 2) (i : Fin 5) :
    rootCoords (K := K) rfl
        (Units.ModPow.map (AdjoinRoot.map (algebraMap ℚ K) f (f.map (algebraMap ℚ K)) dvd_rfl) 2 x)
        i =
      Units.ModPow.map (algebraMap ℚ K : ℚ →* K) 2 (rootCoords map_f_self x i) :=
  AdjoinRoot.modPowEquivPiOfRoots_map _ _ _ _ _ (fun i ↦ by simp) x i

private theorem map_expUnit_algebraMap (K : Type*) [Field K] [CharZero K] (e : Fin 3 → ℕ) :
    Units.ModPow.map (algebraMap ℚ K : ℚ →* K) 2 (expUnit ℚ e) = expUnit K e := by
  rw [Units.ModPow.map_mk]
  congr 1
  ext
  simp [expUnit, baseUnit, Fin.prod_univ_three]

-- The global class with root coordinates `expUnit ℚ (e i)`.
private noncomputable def globalClass (e : Fin 5 → Fin 3 → ℕ) : Units.ModPow (AdjoinRoot f) 2 :=
  (rootCoords map_f_self).symm fun i ↦ expUnit ℚ (e i)

private theorem coords_map_globalClass {K H : Type*} [Field K] [CharZero K] [CommMonoid H]
    {ψ : Units.ModPow K 2 →* H} {h : Fin 3 → H} (hψ : ∀ k, ψ (baseUnit K k) = h k)
    (e : Fin 5 → Fin 3 → ℕ) :
    coords rfl ψ (Units.ModPow.map (AdjoinRoot.map (algebraMap ℚ K) f (f.map (algebraMap ℚ K))
      dvd_rfl) 2 (globalClass e)) = expVec h e := by
  funext i
  rw [coords_apply, rootCoords_map, globalClass, MulEquiv.apply_symm_apply,
    map_expUnit_algebraMap, map_expUnit]
  simp only [hψ, expVec]

private theorem finite_S : S.Finite :=
  (Set.finite_singleton _).insert _

-- The generators `-1`, `2`, `3` of `ℚ(S, 2)`.
private theorem insert_image_S :
    insert ((-1 : ℚˣ) : Units.ModPow ℚ 2) ((fun v ↦ ((Units.mk0
      (Rat.HeightOneSpectrum.natGenerator v : ℚ) (Nat.cast_ne_zero.mpr
        (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero) : ℚˣ) : Units.ModPow ℚ 2)) '' S) =
      Set.range fun k ↦ (baseUnit ℚ k : Units.ModPow ℚ 2) := by
  ext x
  simp [S, baseUnit, Fin.exists_fin_succ, eq_comm]

-- `A(S, 2)` in root coordinates (blueprint `lem:ds-e1-selmer`).
private theorem mem_selmerGroup_iff {y : Units.ModPow (AdjoinRoot f) 2} :
    y ∈ AdjoinRoot.selmerGroup Fact.out S 2 ↔
      ∀ i, rootCoords map_f_self y i ∈
        Subgroup.closure (Set.range fun k ↦ (baseUnit ℚ k : Units.ModPow ℚ 2)) := by
  rw [AdjoinRoot.mem_selmerGroup_iff_of_splits Fact.out α_injective (isRoot_α map_f_self)
    (natDegree_le_of_map_f_eq map_f_self) S 2 y]
  refine forall_congr' fun i ↦ ?_
  rw [rootCoords, AdjoinRoot.modPowEquivPiOfRoots_apply, Rat.selmerGroup_eq_closure finite_S,
    insert_image_S]

private theorem baseUnit_mem_closure (k : Fin 3) :
    (baseUnit ℚ k : Units.ModPow ℚ 2) ∈
      Subgroup.closure (Set.range fun k ↦ (baseUnit ℚ k : Units.ModPow ℚ 2)) :=
  Subgroup.subset_closure ⟨k, rfl⟩

private theorem globalClass_mem_selmerGroup (e : Fin 5 → Fin 3 → ℕ) :
    globalClass e ∈ AdjoinRoot.selmerGroup Fact.out S 2 := by
  refine mem_selmerGroup_iff.mpr fun i ↦ ?_
  rw [globalClass, MulEquiv.apply_symm_apply, expUnit, QuotientGroup.mk_prod]
  exact Subgroup.prod_mem _ fun k _ ↦ by
    rw [QuotientGroup.mk_pow]
    exact Subgroup.pow_mem _ (baseUnit_mem_closure k) _

private theorem eq_empty_of_prod_h₂_eq_one (s : Finset (Fin 3)) (h : ∏ k ∈ s, h₂ k = 1) :
    s = ∅ := by
  decide +revert

private theorem map_baseUnit (K : Type*) [Field K] [CharZero K] (k : Fin 3) :
    Units.ModPow.map (algebraMap ℚ K : ℚ →* K) 2 (baseUnit ℚ k) = baseUnit K k := by
  rw [Units.ModPow.map_mk]
  congr 1
  ext
  fin_cases k <;> simp [baseUnit]

-- The map from `L^× / (L^×)^2` to its analogue over `ℚ_[2]` is injective on `A(S, 2)`: the
-- classes of `-1`, `2`, `3` stay independent over `ℚ_[2]`.
private theorem disjoint_selmerGroup_ker :
    Disjoint (AdjoinRoot.selmerGroup Fact.out S 2) (Units.ModPow.map (AdjoinRoot.map
      (algebraMap ℚ ℚ_[2]) f (f.map (algebraMap ℚ ℚ_[2])) dvd_rfl :
        AdjoinRoot f →* AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) 2).ker := by
  refine Subgroup.disjoint_def.mpr fun {y} hy hρ ↦
    (rootCoords map_f_self).injective (funext fun i ↦ ?_)
  obtain ⟨s, hs⟩ := (Subgroup.mem_closure_range_iff_of_sq_eq_one
    (fun _ ↦ Units.ModPow.pow_eq_one _)).mp (mem_selmerGroup_iff.mp hy i)
  have h := congr(Padic.modPowTwoEquivZModEight (rootCoords rfl $(MonoidHom.mem_ker.mp hρ) i))
  rw [rootCoords_map, ← hs, map_one, Pi.one_apply, map_one, map_prod, map_prod] at h
  simp only [map_baseUnit, modPowTwoEquivZModEight_baseUnit] at h
  rw [map_one, Pi.one_apply, ← hs, eq_empty_of_prod_h₂_eq_one s h, Finset.prod_empty]

private theorem map_descentMap_mumfordClass (K : Type*) [Field K] [CharZero K] (j : Fin 5) :
    Units.ModPow.map (AdjoinRoot.map (algebraMap ℚ K) f (f.map (algebraMap ℚ K)) dvd_rfl) 2
        (HypJac.descentMap f (mumfordClass f (X - C (α j : ℚ)) 0)) =
      HypJac.descentMap (f.map (algebraMap ℚ K)) (mumfordClass _ (X - C (α j : K)) 0) := by
  rw [HypJac.map_descentMap, HypJac.map_mumfordClass]
  simp

private theorem injective_coords {K H : Type*} [Field K] [CharZero K] [CommMonoid H] {g : K[X]}
    (hg : f.map (algebraMap ℚ K) = g) {ψ : Units.ModPow K 2 →* H} (hψ : Function.Injective ψ) :
    Function.Injective (coords hg ψ) :=
  fun _ _ h ↦ (rootCoords hg).injective (funext fun i ↦ hψ congr($h i))

-- The image of the global class `P` over `ℚ_[2]` is the class of `4 - θ`.
private theorem map_globalClass_pExp {u : (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2])))ˣ}
    (hu : (u : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) = AdjoinRoot.of _ 4 - AdjoinRoot.root _) :
    Units.ModPow.map (AdjoinRoot.map (algebraMap ℚ ℚ_[2]) f (f.map (algebraMap ℚ ℚ_[2])) dvd_rfl) 2
      (globalClass pExp) = (u : Units.ModPow (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) 2) :=
  injective_coords rfl Padic.modPowTwoEquivZModEight.injective
    ((coords_map_globalClass modPowTwoEquivZModEight_baseUnit pExp).trans (coords_four hu).symm)

-- The image of the global class `Q` over `ℚ_[2]` is the class of `1 / 5 - θ`.
private theorem map_globalClass_qExp {u : (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2])))ˣ}
    (hu : (u : AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) =
      AdjoinRoot.of _ 5⁻¹ - AdjoinRoot.root _) :
    Units.ModPow.map (AdjoinRoot.map (algebraMap ℚ ℚ_[2]) f (f.map (algebraMap ℚ ℚ_[2])) dvd_rfl) 2
      (globalClass qExp) = (u : Units.ModPow (AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) 2) :=
  injective_coords rfl Padic.modPowTwoEquivZModEight.injective
    ((coords_map_globalClass modPowTwoEquivZModEight_baseUnit qExp).trans (coords_inv_five hu).symm)

-- Under (Loc) for `ℚ_[2]`, a class of `A(S, 2)` satisfying the local condition at `ℚ_[2]` lies
-- in the subgroup generated by the values at the points `(α j, 0)` and the global classes `P`,
-- `Q`, as the map to `ℚ_[2]` is injective on `A(S, 2)`.
private theorem mem_closure_of_mem_localCondition_two
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    {y : Units.ModPow (AdjoinRoot f) 2} (hA : y ∈ AdjoinRoot.selmerGroup Fact.out S 2)
    (h2 : y ∈ HypJac.localCondition f ℚ_[2]) :
    y ∈ Subgroup.closure (Set.range (fun j ↦ HypJac.descentMap f (mumfordClass f (X - C (α j : ℚ))
      0)) ∪ {globalClass pExp, globalClass qExp}) := by
  set T := Set.range (fun j ↦ HypJac.descentMap f (mumfordClass f (X - C (α j : ℚ)) 0)) ∪
    {globalClass pExp, globalClass qExp}
  have h4 := (AdjoinRoot.isUnit_of_sub_root (f := f.map (algebraMap ℚ ℚ_[2])) (x₀ := 4)
    (by rw [eval_four]; norm_num)).unit_spec
  have h5 := (AdjoinRoot.isUnit_of_sub_root (f := f.map (algebraMap ℚ ℚ_[2])) (x₀ := 5⁻¹)
    (by rw [eval_inv_five]; norm_num)).unit_spec
  have hle : Subgroup.closure T ≤ AdjoinRoot.selmerGroup Fact.out S 2 :=
    (Subgroup.closure_le _).mpr (Set.union_subset (Set.range_subset_iff.mpr fun j ↦
      HypJac.range_descentMap_le_selmerGroup f (fun _ ↦ hasSeparableReduction_of_notMem) ⟨_, rfl⟩)
        (Set.pair_subset (globalClass_mem_selmerGroup _) (globalClass_mem_selmerGroup _)))
  obtain ⟨t, ht, hty⟩ : Units.ModPow.map (AdjoinRoot.map (algebraMap ℚ ℚ_[2]) f
      (f.map (algebraMap ℚ ℚ_[2])) dvd_rfl) 2 y ∈ (Subgroup.closure T).map (Units.ModPow.map
        (AdjoinRoot.map (algebraMap ℚ ℚ_[2]) f (f.map (algebraMap ℚ ℚ_[2])) dvd_rfl :
          AdjoinRoot f →* AdjoinRoot (f.map (algebraMap ℚ ℚ_[2]))) 2) := by
    rw [MonoidHom.map_closure, Set.image_union, Set.image_pair, ← Set.range_comp,
      map_globalClass_pExp h4, map_globalClass_qExp h5]
    simp only [Function.comp_def, map_descentMap_mumfordClass]
    rw [← range_descentMap_two L₂ h4 h5]
    exact (HypJac.mem_localCondition_iff f ℚ_[2]).mp h2
  exact (MonoidHom.disjoint_ker_iff_injOn.mp disjoint_selmerGroup_ker (hle ht) hA hty) ▸ ht

private theorem eq_empty_of_prod_eq_prod_three (s : Finset (Fin 2)) (t : Finset (Fin 5))
    (h : ∏ k ∈ s, ![expVec h₃ pExp, expVec h₃ qExp] k = ∏ j ∈ t, expVec h₃ (torsionExp j)) :
    s = ∅ := by
  decide +kernel +revert

-- Under (Loc) for `ℚ_[3]`, the only class of the subgroup generated by `P`, `Q` that satisfies
-- the local condition at `ℚ_[3]` is `1`.
private theorem eq_one_of_mem_localCondition_three
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2)
    {z : Units.ModPow (AdjoinRoot f) 2}
    (hz : z ∈ Subgroup.closure {globalClass pExp, globalClass qExp})
    (h3 : z ∈ HypJac.localCondition f ℚ_[3]) : z = 1 := by
  rw [← Matrix.range_cons_cons_empty _ _ ![], Subgroup.mem_closure_range_iff_of_sq_eq_one
    (fun _ ↦ Units.ModPow.pow_eq_one _)] at hz
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨t, ht⟩ := (Subgroup.mem_closure_range_iff_of_sq_eq_one
    (fun _ ↦ Units.ModPow.pow_eq_one _)).mp
      (range_descentMap_three L₃ ▸ (HypJac.mem_localCondition_iff f ℚ_[3]).mp h3)
  have h := congr(coords rfl ψ₃ $ht)
  simp only [map_prod] at h
  rw [eq_empty_of_prod_eq_prod_three s t ?_, Finset.prod_empty]
  rwa [Finset.prod_congr rfl fun j _ ↦ coords_descentMap_mumfordClass rfl ψ₃_baseUnit j, eq_comm,
    Finset.prod_congr rfl fun k _ ↦ ?_] at h
  fin_cases k
  exacts [coords_map_globalClass ψ₃_baseUnit pExp, coords_map_globalClass ψ₃_baseUnit qExp]

/-- **The relaxed Selmer group of E1** (blueprint `prop:ds-e1-sel`): under (Loc) for `ℚ_[2]` and
`ℚ_[3]`, the relaxed Selmer group for `S = {2, 3}` and the local conditions at `ℚ_[2]` and `ℚ_[3]`
is the image of `J(ℚ)[2]` under the `x - T` map. By
`ChabautyColeman.DescentExample1.range_descentMap_two`, a class of it lies in the subgroup generated
by the values at the points `(α j, 0)` and two global classes `P`, `Q` with the images of `4 - θ`
and `1 / 5 - θ` over `ℚ_[2]`; by `ChabautyColeman.DescentExample1.range_descentMap_three`, the local
condition at `ℚ_[3]` excludes `P`, `Q` and `P * Q`. -/
theorem relaxedSelmerGroup_eq
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2) :
    relaxedSelmerGroup f S (fun i : Fin 2 ↦ ℚ_[![2, 3] i]) =
      (powMonoidHom 2 : HypJac ℚ f →* HypJac ℚ f).ker.map (HypJac.descentMap f) := by
  refine le_antisymm (fun y hy ↦ ?_) ((Subgroup.map_le_range _ _).trans
    (range_descentMap_le_relaxedSelmerGroup _ fun _ ↦ hasSeparableReduction_of_notMem))
  obtain ⟨⟨hA, -⟩, hloc⟩ := hy
  have hloc := Subgroup.mem_iInf.mp hloc
  have hy := mem_closure_of_mem_localCondition_two L₂ hA (hloc 0)
  rw [Subgroup.closure_union] at hy
  obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup.mp hy
  have hwμ : w ∈ (powMonoidHom 2 : HypJac ℚ f →* HypJac ℚ f).ker.map (HypJac.descentMap f) :=
    (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr fun j ↦ Subgroup.mem_map.mpr
      ⟨_, MonoidHom.mem_ker.mpr (mumfordClass_zero_sq f
        (dvd_iff_isRoot.mpr (isRoot_α map_f_self j))), rfl⟩) hw
  rwa [eq_one_of_mem_localCondition_three L₃ hz ((Subgroup.mul_mem_cancel_left _
    (HypJac.range_descentMap_le_localCondition f ℚ_[3] (Subgroup.map_le_range _ _ hwμ))).mp
      (hloc 1)), mul_one]

/-! ### The group `J̃(𝔽₅)` (blueprint `lem:ds-e1-five`) -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

instance neZero_two_zmod_five : NeZero (2 : ZMod 5) := ⟨by decide⟩

private theorem natDegree_X_pow_five_sub_X : (X ^ 5 - X : (ZMod 5)[X]).natDegree = 5 :=
  natDegree_X_pow_sub_X Nat.one_lt_ofNat

instance fact_odd_natDegree_X_pow_five_sub_X : Fact (Odd (X ^ 5 - X : (ZMod 5)[X]).natDegree) :=
  ⟨⟨2, natDegree_X_pow_five_sub_X⟩⟩

instance fact_squarefree_X_pow_five_sub_X : Fact (Squarefree (X ^ 5 - X : (ZMod 5)[X])) :=
  ⟨(galois_poly_separable 5 5 dvd_rfl).squarefree⟩

-- For `u = X ^ 2 + b X + c` and `v = d X + e`, the remainder of `v ^ 2 - (X ^ 5 - X)` modulo `u`
-- is `r₁ X + r₀` with the coefficients below, over any commutative ring.
private theorem dvd_sq_sub_X_pow_five_sub_X_iff {R : Type*} [CommRing R] (b c d e : R) :
    X ^ 2 + C b * X + C c ∣ (C d * X + C e) ^ 2 - (X ^ 5 - X) ↔
      X ^ 2 + C b * X + C c ∣ C (2 * d * e - b * d ^ 2 - b ^ 4 + 3 * b ^ 2 * c - c ^ 2 + 1) * X +
        C (e ^ 2 - c * d ^ 2 - b ^ 3 * c + 2 * b * c ^ 2) := by
  have h : (C d * X + C e) ^ 2 - (X ^ 5 - X) = (X ^ 2 + C b * X + C c) *
      (-X ^ 3 + C b * X ^ 2 + C (c - b ^ 2) * X + C (d ^ 2 + b ^ 3 - 2 * b * c)) +
        (C (2 * d * e - b * d ^ 2 - b ^ 4 + 3 * b ^ 2 * c - c ^ 2 + 1) * X +
          C (e ^ 2 - c * d ^ 2 - b ^ 3 * c + 2 * b * c ^ 2)) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
    ring
  rw [h, dvd_add_right (dvd_mul_right _ _)]

-- The remainder `r₁ X + r₀` vanishes over `𝔽₅` only for `d = e = 0`: a check of the `5 ^ 4`
-- tuples.
private theorem eq_zero_of_remainder_eq_zero {b c d e : ZMod 5}
    (h₁ : 2 * d * e - b * d ^ 2 - b ^ 4 + 3 * b ^ 2 * c - c ^ 2 + 1 = 0)
    (h₀ : e ^ 2 - c * d ^ 2 - b ^ 3 * c + 2 * b * c ^ 2 = 0) : d = 0 ∧ e = 0 := by
  decide +revert

private theorem eq_zero_of_quadratic_dvd_sq_sub (b c : ZMod 5) {v : (ZMod 5)[X]}
    (hv : v.degree < (X ^ 2 + C b * X + C c).degree)
    (h : X ^ 2 + C b * X + C c ∣ v ^ 2 - (X ^ 5 - X)) : v = 0 := by
  have hu : (X ^ 2 + C b * X + C c).degree = 2 := by compute_degree!
  have hv' := eq_X_add_C_of_degree_le_one (Order.le_of_lt_succ (hu ▸ hv))
  rw [hv', dvd_sq_sub_X_pow_five_sub_X_iff] at h
  obtain ⟨h₁, h₀⟩ := C_mul_X_add_C_eq_zero.mp
    (eq_zero_of_dvd_of_degree_lt h (degree_linear_lt.trans_eq hu.symm))
  obtain ⟨hd, he⟩ := eq_zero_of_remainder_eq_zero h₁ h₀
  simpa [hd, he] using hv'

-- A reduced Mumford pair `(u, v)` with `u ∣ v ^ 2 - (X ^ 5 - X)` over `𝔽₅` has `v = 0`: for
-- `u = X - a`, as `a ^ 5 = a`; for `deg u = 2`, by `eq_zero_of_quadratic_dvd_sq_sub`.
private theorem eq_zero_of_dvd_sq_sub {u v : (ZMod 5)[X]} (hu : u.Monic) (hd : u.natDegree ≤ 2)
    (hv : v.degree < u.degree) (h : u ∣ v ^ 2 - (X ^ 5 - X)) : v = 0 := by
  obtain h0 | h1 | h2 : u.natDegree = 0 ∨ u.natDegree = 1 ∨ u.natDegree = 2 := by lia
  · exact eq_zero_of_dvd_of_degree_lt (hu.natDegree_eq_zero.mp h0 ▸ one_dvd v) hv
  · obtain ⟨a, rfl⟩ := isMonicOfDegree_one_iff.mp ⟨h1, hu⟩
    rw [← sub_neg_eq_add, ← map_neg] at h hv
    have hg : X - C (-a) ∣ X ^ 5 - X := dvd_iff_isRoot.mpr (by simp [ZMod.pow_card])
    exact eq_zero_of_dvd_of_degree_lt
      ((prime_X_sub_C (-a)).dvd_of_dvd_pow (n := 2) ((dvd_sub_left hg).mp h)) hv
  · obtain ⟨b, c, rfl⟩ := isMonicOfDegree_two_iff.mp ⟨h2, hu⟩
    exact eq_zero_of_quadratic_dvd_sq_sub b c hv h

/-- Every element of `J̃(𝔽₅)`, for the curve `y ^ 2 = x ^ 5 - x`, has order dividing `2`: its
reduced Mumford representative `(u, v)` has `v = 0`. -/
theorem sq_eq_one_of_eq_X_pow_five_sub_X {g : (ZMod 5)[X]} [Fact (Odd g.natDegree)]
    (hg : g = X ^ 5 - X) (x : HypJac (ZMod 5) g) : x ^ 2 = 1 := by
  subst hg
  obtain ⟨u, v, hm, hlt, hred, hdvd, rfl⟩ := exists_mk0_mumfordIdeal_reduced _ x
  rw [← mumfordClass_eq_mk0]
  obtain rfl : v = 0 := eq_zero_of_dvd_sq_sub hm (by lia [natDegree_X_pow_five_sub_X]) hlt hdvd
  exact mumfordClass_zero_sq _ (by rwa [zero_pow two_ne_zero, zero_sub, dvd_neg] at hdvd)

/-- The group `J̃(𝔽₅)` of the curve `y ^ 2 = x ^ 5 - x` has exponent `2`
(`ChabautyColeman.DescentExample1.sq_eq_one_of_eq_X_pow_five_sub_X`, and the class `[x, 0]` of the
point `(0, 0)` is not trivial); so it is `J̃(𝔽₅)[2]`, of order `16` by
`ChabautyColeman.HypJac.card_ker_powMonoidHom_two`. -/
theorem exponent_hypJac_zmod_five {g : (ZMod 5)[X]} [Fact (Odd g.natDegree)]
    (hg : g = X ^ 5 - X) : Monoid.exponent (HypJac (ZMod 5) g) = 2 := by
  refine ((Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one
    (sq_eq_one_of_eq_X_pow_five_sub_X hg))).resolve_left fun h ↦ X_ne_C (1 : ZMod 5) ?_
  subst hg
  have := Monoid.exp_eq_one_iff.mp h
  refine ((mumfordClass_zero_inj (X ^ 5 - X : (ZMod 5)[X]) monic_X monic_one
    (X_dvd_iff.mpr (by simp)) (one_dvd _) ?_ ?_).mp (Subsingleton.elim _ _)).trans C_1.symm <;>
    simp [natDegree_X_pow_five_sub_X]

/-! ### `J(ℚ)` and `C(ℚ)` (blueprint `thm:ds-e1`) -/

theorem map_F_zmod_five : F.map (Int.castRingHom (ZMod 5)) = X ^ 5 - X := by
  simp only [F, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
    Polynomial.map_mul, Polynomial.map_ofNat]
  reduce_mod_char

instance fact_odd_natDegree_map_F_rat : Fact (Odd (F.map (Int.castRingHom ℚ)).natDegree) :=
  map_F ▸ inferInstance

instance fact_odd_natDegree_map_F_zmod_five :
    Fact (Odd (F.map (Int.castRingHom (ZMod 5))).natDegree) :=
  map_F_zmod_five ▸ inferInstance

-- Every element of `J(ℚ)` that is a `2 ^ n`-th power for every `n` has odd order: its image in
-- `J(ℚ_[2])` does, by (Loc) for `ℚ_[2]`.
private theorem coprime_orderOf_of_mem_iInf
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2) {x : HypJac ℚ f}
    (hx : x ∈ ⨅ n : ℕ, (powMonoidHom (2 ^ n) : HypJac ℚ f →* HypJac ℚ f).range) :
    (orderOf x).Coprime 2 :=
  MonoidHom.coprime_orderOf_of_mem_iInf_range_powMonoidHom_pow
    (f := HypJac.map (K' := ℚ_[2]) f) (hypJac_map_injective f)
    (fun _ hy ↦ L₂.mem_iInf_range_powMonoidHom_pow_iff.mp hy) hx

-- `J(ℚ) = J(ℚ)[2] ⊔ 2 J(ℚ)`, by blueprint `prop:ds-e1-sel` and the kernel of the `x - T` map.
private theorem ker_sup_range_powMonoidHom_two_eq_top
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2) :
    (powMonoidHom 2 : HypJac ℚ f →* HypJac ℚ f).ker ⊔ (powMonoidHom 2).range = ⊤ := by
  refine eq_top_iff.mpr fun a _ ↦ ?_
  obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ((relaxedSelmerGroup_eq L₂ L₃).le
    (range_descentMap_le_relaxedSelmerGroup _ (fun _ ↦ hasSeparableReduction_of_notMem) ⟨a, rfl⟩))
  have h : γ⁻¹ * a ∈ (HypJac.descentMap f).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [HypJac.ker_descentMap] at h
  exact mul_inv_cancel_left γ a ▸ Subgroup.mul_mem_sup hγ h

-- `J(ℚ)` is a torsion group: modulo the finite group `J(ℚ)[2]`, every element has odd order, as
-- `J(ℚ) = J(ℚ)[2] ⊔ 2 ^ n J(ℚ)` for every `n`.
private theorem isMulTorsion_hypJac
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2) :
    IsMulTorsion (HypJac ℚ f) := by
  have : Finite (powMonoidHom 2 : HypJac ℚ f →* HypJac ℚ f).ker :=
    Nat.finite_of_card_ne_zero (by rw [card_ker_powMonoidHom_two_of_map_f_eq map_f_self]; norm_num)
  refine IsMulTorsion.extension_closed (N := (powMonoidHom 2 : HypJac ℚ f →* HypJac ℚ f).ker)
    (QuotientGroup.ker_mk' _).symm (fun x ↦ ?_) isMulTorsion_of_finite
  induction x using QuotientGroup.induction_on with | H a => ?_
  have h := Subgroup.coprime_orderOf_mk_of_mem_iInf_sup_range_powMonoidHom_pow
    (fun _ ↦ coprime_orderOf_of_mem_iInf L₂) (Subgroup.mem_iInf.mpr fun n ↦
      (Subgroup.sup_range_powMonoidHom_pow_eq_top (ker_sup_range_powMonoidHom_two_eq_top L₂ L₃)
        n).symm ▸ Subgroup.mem_top a)
  exact orderOf_pos_iff.mp (Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at h)

/-- **`J(ℚ) = J(ℚ)[2]` for E1** (blueprint `thm:ds-e1`): under (Loc) for `ℚ_[2]` and `ℚ_[3]` and
(Red) for `p = 5`, every point of `J(ℚ)` has order dividing `2`. By
`ChabautyColeman.DescentExample1.relaxedSelmerGroup_eq`, `J(ℚ) = J(ℚ)[2] + 2^n J(ℚ)` for every `n`,
so every point is of odd order modulo the finite group `J(ℚ)[2]`
(`Subgroup.coprime_orderOf_mk_of_mem_iInf_sup_range_powMonoidHom_pow`), and `J(ℚ)` is a torsion
group (`IsMulTorsion.extension_closed`); reduction modulo `5` into `J̃(𝔽₅)`, of exponent `2`, kills
the square of each point. -/
theorem ker_powMonoidHom_two_eq_top
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2)
    (R₅ : HypJac.TorsionReduction 5 F) :
    (powMonoidHom 2 : HypJac ℚ f →* HypJac ℚ f).ker = ⊤ :=
  eq_top_iff.mpr fun a _ ↦ R₅.pow_eq_one_of_isOfFinOrder map_F map_F_zmod_five
    (sq_eq_one_of_eq_X_pow_five_sub_X rfl) (isMulTorsion_hypJac L₂ L₃ a)

/-- Under (Loc) for `ℚ_[2]` and `ℚ_[3]` and (Red) for `p = 5`, `J(ℚ) = J(ℚ)[2]` has `16` elements
(`ChabautyColeman.DescentExample1.ker_powMonoidHom_two_eq_top`). -/
theorem card_hypJac
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2)
    (R₅ : HypJac.TorsionReduction 5 F) :
    Nat.card (HypJac ℚ f) = 16 := by
  rw [← Subgroup.card_top, ← ker_powMonoidHom_two_eq_top L₂ L₃ R₅,
    card_ker_powMonoidHom_two_of_map_f_eq map_f_self]

-- A rational point `(x₀, y₀)` with `[(x₀, y₀) - ∞]` of order dividing `2` has `y₀ = 0`: the
-- reduced Mumford representatives `(x - x₀, y₀)` and `(x - x₀, -y₀)` of the class and its inverse
-- agree.
private theorem eq_zero_of_mumfordClass_sq_eq_one {x₀ y₀ : ℚ} (h : y₀ ^ 2 = f.eval x₀)
    (hsq : mumfordClass f (X - C x₀) (C y₀) ^ 2 = 1) : y₀ = 0 := by
  have hdvd : X - C x₀ ∣ C y₀ ^ 2 - f := dvd_iff_isRoot.mpr (by simp [h])
  have hdeg : (C y₀).degree < (X - C x₀).degree := by
    rw [degree_X_sub_C]
    exact degree_C_le.trans_lt zero_lt_one
  have hg : 2 * (X - C x₀).natDegree < f.natDegree := by
    rw [natDegree_X_sub_C, natDegree_f]
    norm_num
  have hneg := ((mumfordClass_inj f (monic_X_sub_C x₀) (monic_X_sub_C x₀) hdeg
    (by rwa [degree_neg]) hg hg hdvd (by rwa [neg_sq])).mp
      (by rw [mumfordClass_neg f hdvd, eq_inv_iff_mul_eq_one, ← sq, hsq])).2
  exact self_eq_neg.mp (C_inj.mp (hneg.trans C_neg.symm))

/-- **The rational points of E1** (blueprint `thm:ds-e1`): under (Loc) for `ℚ_[2]` and `ℚ_[3]`
and (Red) for `p = 5`, the affine rational points of `y ^ 2 = x (x ^ 2 - 1) (x ^ 2 - 9)` are the
five points `(α, 0)`, so `C(ℚ) = {∞, (0, 0), (± 1, 0), (± 3, 0)}`: for a rational point
`(x₀, y₀)`, `[(x₀, y₀) - ∞]` has order dividing `2`
(`ChabautyColeman.DescentExample1.ker_powMonoidHom_two_eq_top`), which forces `y₀ = 0`. -/
theorem ratPoints_eq
    (L₂ : HypJac.LocalStructure 2 ℚ_[2] (f.map (algebraMap ℚ ℚ_[2])) 2)
    (L₃ : HypJac.LocalStructure 3 ℚ_[3] (f.map (algebraMap ℚ ℚ_[3])) 2)
    (R₅ : HypJac.TorsionReduction 5 F) :
    {P : ℚ × ℚ | P.2 ^ 2 = f.eval P.1} = {(-3, 0), (-1, 0), (0, 0), (1, 0), (3, 0)} := by
  ext ⟨x₀, y₀⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl := eq_zero_of_mumfordClass_sq_eq_one h (MonoidHom.mem_ker.mp
      ((ker_powMonoidHom_two_eq_top L₂ L₃ R₅).ge (Subgroup.mem_top _)))
    have h0 : (f.map (algebraMap ℚ ℚ)).eval x₀ = 0 := by simpa [eq_comm] using h
    rw [map_f_eq_prod, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    fin_cases i <;> simp [α, sub_eq_zero, add_eq_zero_iff_eq_neg] at hi <;> simp [hi]
  · rcases h with h | h | h | h | h <;> simp [Prod.ext_iff] at h <;> norm_num [h, f]

end ChabautyColeman.DescentExample1

end
