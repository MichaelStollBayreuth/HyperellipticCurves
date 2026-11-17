/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import HyperellipticCurves.Mathlib.NumberTheory.Padics.PadicIntegers
public import HyperellipticCurves.Mathlib.RingTheory.DiscreteValuationRing.UnitsModPow
public import HyperellipticCurves.Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms

import HyperellipticCurves.Mathlib.Algebra.Group.Prod
import HyperellipticCurves.Mathlib.Algebra.Polynomial.SpecificDegree
import HyperellipticCurves.Mathlib.NumberTheory.Padics.PadicNumbers
import HyperellipticCurves.Mathlib.NumberTheory.Padics.RingHoms
import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot

/-!
# Square classes of `ℚ_[p]`

A unit of `ℤ_[2]` is a square exactly when it is `1` modulo `8`, by Hensel's lemma. Hence
`ℚ_[2]ˣ/(ℚ_[2]ˣ)² ≅ ℤ/2 × (ℤ/8)ˣ`, and, for odd `p`, `ℚ_[p]ˣ/(ℚ_[p]ˣ)² ≅ ℤ/2 × (ℤ/p)ˣ/((ℤ/p)ˣ)²`
(`IsDiscreteValuationRing.modPowTwoEquiv`).

## Main statements

* `PadicInt.isSquare_iff_toZModPow_three_eq_one`: a unit `u` of `ℤ_[2]` is a square if and only
  if `u ≡ 1 mod 8`.
* `Padic.modPowTwoEquivZModEight`: `ℚ_[2]ˣ/(ℚ_[2]ˣ)² ≃* ℤ/2 × (ℤ/8)ˣ`, by
  `2 ^ n * u ↦ (n mod 2, u mod 8)`; its values are `Padic.modPowTwoEquivZModEight_mk_of_val_eq`.
* `Padic.modPowTwoEquiv`: `ℚ_[p]ˣ/(ℚ_[p]ˣ)² ≃* ℤ/2 × (ℤ/p)ˣ/((ℤ/p)ˣ)²` for odd `p`, by
  `p ^ n * u ↦ (n mod 2, u mod p)`; its values are `Padic.modPowTwoEquiv_mk_of_eq_pow_mul` and,
  for integers, `Padic.modPowTwoEquiv_mk_of_val_eq`.
* `Padic.finite_modPow_two`: `ℚ_[p]ˣ/(ℚ_[p]ˣ)²` is finite.
* `PadicInt.exists_aeval_eq_zero_toZModPow_eq`: Hensel's lemma with a congruence: a root `z ≡ a`
  modulo `p ^ k` of `F` if `F(a) ≡ 0` and `F'(a)` is a unit.
* `PadicInt.norm_aeval_eq_of_aeval_eq_zero`: near a root `z` of `F`, `‖F(a)‖ = ‖z - a‖ * ‖F'(z)‖`.
* `Padic.modPowTwoEquiv_mk_of_toZModPow_eq`: the value of `Padic.modPowTwoEquiv` on a `p`-adic
  integer given modulo a power of `p`.
* `Padic.irreducible_X_sq_add_C_mul_X_add_C_of_odd_valuation`,
  `Padic.not_isSquare_adjoinRoot_of_odd_valuation`: a monic quadratic over `ℚ_[p]` whose
  discriminant has odd valuation is irreducible, and a criterion for `u + w θ` not to be a square
  in the quotient by it.
* `Padic.modPowTwoEquivZModTwo`: for odd `p`,
  `ℚ_[p]ˣ/(ℚ_[p]ˣ)² ≃* Multiplicative (ZMod 2 × ZMod 2)`, the valuation modulo `2` and whether the
  unit part is a nonsquare modulo `p`.
* `Padic.modPowTwoEquivZModTwo_mk_of_toZModPow_two_eq`: its value on the class of `c ^ 2 * y` for
  `y` given modulo `p ^ 2`, in terms of the computable `Padic.modPowTwoCoords`.
* `Padic.isSquare_iff_modPowTwoCoords_eq_zero`: `c ^ 2 * y`, `c ≠ 0`, is a square if and only if
  `Padic.modPowTwoCoords p z = 0` for the residue `z ≠ 0` of `y ∈ ℤ_[p]` modulo `p ^ 2`.
-/

@[expose] public section

open Polynomial

namespace PadicInt

/-- A unit of `ℤ_[2]` is a square exactly when it is `1` modulo `8`: the square of a unit of
`ℤ/8` is `1`, and conversely `hensels_lemma` applies to `X ^ 2 - u` at `1`, as
`‖1 - u‖ ≤ 2⁻³ < ‖2‖²`. -/
theorem isSquare_iff_toZModPow_three_eq_one {u : ℤ_[2]} (hu : IsUnit u) :
    IsSquare u ↔ toZModPow 3 u = 1 := by
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun h ↦ ?_⟩
  · have := (isUnit_toZModPow_iff three_ne_zero).mpr (isUnit_of_mul_isUnit_left (ha ▸ hu))
    rw [ha, map_mul]
    exact congr(Units.val $((by decide : ∀ b : (ZMod (2 ^ 3))ˣ, b * b = 1) this.unit))
  · have h1 := (norm_le_pow_iff_mem_span_pow (1 - u) 3).mpr (by
      rw [← ker_toZModPow, RingHom.mem_ker, map_sub, map_one, h, sub_self])
    obtain ⟨z, hz, -⟩ := hensels_lemma (F := X ^ 2 - C u) (a := (1 : ℤ_[2])) <| by
      simp only [map_sub, aeval_X_pow, aeval_C, one_pow, derivative_X_pow, derivative_C, sub_zero,
        aeval_mul, mul_one, Algebra.algebraMap_self, RingHom.id_apply, map_natCast, norm_p]
      exact h1.trans_lt (by norm_num)
    exact ⟨z, by simpa [sub_eq_zero, sq, eq_comm] using hz⟩

/-- The units of `ℤ_[2]` modulo squares are the units of `ℤ/8`
(`PadicInt.isSquare_iff_toZModPow_three_eq_one`). -/
noncomputable def modPowTwoEquivZModEight : Units.ModPow ℤ_[2] 2 ≃* (ZMod 8)ˣ :=
  QuotientGroup.liftEquiv _ (φ := Units.map (toZModPow (p := 2) 3 : ℤ_[2] →* ZMod (2 ^ 3)))
    (fun w ↦ by
      obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (toZModPow (p := 2) 3) w
      exact ⟨((isUnit_toZModPow_iff three_ne_zero).mp (hx ▸ w.isUnit)).unit, Units.ext hx⟩) <| by
    ext u
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff, Units.ModPow.mk_eq_one_iff_isSquare,
      isSquare_iff_toZModPow_three_eq_one u.isUnit, Units.ext_iff]
    rfl

@[simp]
theorem modPowTwoEquivZModEight_mk (u : ℤ_[2]ˣ) :
    modPowTwoEquivZModEight u = Units.map (toZModPow (p := 2) 3 : ℤ_[2] →* ZMod (2 ^ 3)) u :=
  rfl

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]] {F : R[X]}

/-- Near a root `z` of `F`, closer to `a` than `F'(z)` is to `0`, the value `F(a)` has norm
`‖z - a‖ * ‖F'(z)‖`, by the Taylor expansion of `F` at `z`. -/
theorem norm_aeval_eq_of_aeval_eq_zero {a z : ℤ_[p]} (hz : F.aeval z = 0)
    (h : ‖z - a‖ < ‖F.derivative.aeval z‖) :
    ‖F.aeval a‖ = ‖z - a‖ * ‖F.derivative.aeval z‖ := by
  obtain ⟨c, hc⟩ := binomExpansion (F.map (algebraMap R ℤ_[p])) z (a - z)
  rw [add_sub_cancel, derivative_map] at hc
  simp only [eval_map_algebraMap, hz, zero_add] at hc
  have hlt : ‖c * (a - z)‖ < ‖F.derivative.aeval z‖ := by
    rw [norm_mul, norm_sub_rev]
    exact (mul_le_of_le_one_left (norm_nonneg _) c.norm_le_one).trans_lt h
  have hfac : F.aeval a = (a - z) * (F.derivative.aeval z + c * (a - z)) := by
    linear_combination hc
  rw [hfac, norm_mul, norm_sub_rev, norm_add_eq_max_of_ne hlt.ne', max_eq_left hlt.le]

/-- **Hensel's lemma** with a congruence: if `F(a) ≡ 0 mod p ^ k`, `k ≠ 0`, and `F'(a)` is a unit,
then `F` has a root `z ≡ a mod p ^ k` (from `hensels_lemma` and
`PadicInt.norm_aeval_eq_of_aeval_eq_zero`). -/
theorem exists_aeval_eq_zero_toZModPow_eq {a : ℤ_[p]} {k : ℕ} (hk : k ≠ 0)
    (ha : toZModPow k (F.aeval a) = 0) (hF : IsUnit (F.derivative.aeval a)) :
    ∃ z : ℤ_[p], F.aeval z = 0 ∧ toZModPow k z = toZModPow k a := by
  rw [isUnit_iff] at hF
  rw [← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow] at ha
  obtain ⟨z, hz, hza, hz', -⟩ := hensels_lemma (F := F) (a := a) <| by
    rw [hF, one_pow]
    exact ha.trans_lt (zpow_lt_one_of_neg₀ (mod_cast (Fact.out : p.Prime).one_lt) (by lia))
  refine ⟨z, hz, ?_⟩
  rw [hF] at hza hz'
  have := norm_aeval_eq_of_aeval_eq_zero hz (hz'.symm ▸ hza)
  rw [hz', mul_one] at this
  rwa [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_toZModPow,
    ← norm_le_pow_iff_mem_span_pow, ← this]

end PadicInt

namespace Padic

/-- **Square classes of `ℚ_[2]`**: by `2 ^ n * u ↦ (n mod 2, u mod 8)`, `ℚ_[2]ˣ/(ℚ_[2]ˣ)²` is
`ℤ/2 × (ℤ/8)ˣ`, of order `8` (`PadicInt.isSquare_iff_toZModPow_three_eq_one`). -/
noncomputable def modPowTwoEquivZModEight :
    Units.ModPow ℚ_[2] 2 ≃* Multiplicative (ZMod 2) × (ZMod 8)ˣ :=
  (IsDiscreteValuationRing.modPowEquiv ℚ_[2] PadicInt.irreducible_p 2).trans
    ((MulEquiv.refl _).prodCongr PadicInt.modPowTwoEquivZModEight)

/-- The value of `Padic.modPowTwoEquivZModEight` on the class of `2 ^ n * m` for an odd integer
`m`, whose residue class modulo `8` is the unit `w`. -/
theorem modPowTwoEquivZModEight_mk_of_val_eq {x : ℚ_[2]ˣ} (n : ℕ) (m : ℤ) (w : (ZMod 8)ˣ)
    (hx : (x : ℚ_[2]) = 2 ^ n * m) (hw : (w : ZMod 8) = m) :
    modPowTwoEquivZModEight x = (.ofAdd (n : ZMod 2), w) := by
  have hm : IsUnit (m : ℤ_[2]) :=
    (PadicInt.isUnit_toZModPow_iff three_ne_zero).mp (by simp [← hw])
  rw [modPowTwoEquivZModEight, MulEquiv.trans_apply,
    IsDiscreteValuationRing.modPowEquiv_mk_of_val_eq _ 2 (m := n) (u := hm.unit) (by simp [hx])]
  simp [Units.ext_iff, ← hw]

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Square classes of `ℚ_[p]`** for an odd prime `p`: by `p ^ n * u ↦ (n mod 2, u mod p)`,
`ℚ_[p]ˣ/(ℚ_[p]ˣ)²` is `ℤ/2 × (ℤ/p)ˣ/((ℤ/p)ˣ)²` (`IsDiscreteValuationRing.modPowTwoEquiv`). -/
noncomputable def modPowTwoEquiv (hp2 : p ≠ 2) :
    Units.ModPow ℚ_[p] 2 ≃* Multiplicative (ZMod 2) × Units.ModPow (ZMod p) 2 :=
  (IsDiscreteValuationRing.modPowTwoEquiv ℚ_[p]
    (PadicInt.isUnit_natCast_iff.mpr ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2))
    PadicInt.irreducible_p).trans
    ((MulEquiv.refl _).prodCongr (Units.ModPow.congr PadicInt.residueField.toMulEquiv 2))

variable {p}

/-- The value of `Padic.modPowTwoEquiv` on the class of `p ^ n * u` for `u ∈ ℤ_[p]` whose residue
modulo `p` is the unit `w`. -/
theorem modPowTwoEquiv_mk_of_eq_pow_mul (hp2 : p ≠ 2) {x : ℚ_[p]ˣ} (n : ℕ) (u : ℤ_[p])
    (w : (ZMod p)ˣ) (hx : (x : ℚ_[p]) = p ^ n * u) (hw : PadicInt.toZMod u = w) :
    modPowTwoEquiv p hp2 x = (.ofAdd (n : ZMod 2), (w : Units.ModPow (ZMod p) 2)) := by
  have hu : IsUnit u := (isUnit_map_iff PadicInt.toZMod _).mp (hw ▸ w.isUnit)
  rw [modPowTwoEquiv, MulEquiv.trans_apply, IsDiscreteValuationRing.modPowTwoEquiv_mk_of_val_eq
    _ _ (m := n) (u := hu.unit) (by simp [hx]), MulEquiv.prodCongr_apply, Units.ModPow.congr_mk]
  exact Prod.ext (by simp) congr(QuotientGroup.mk $(Units.ext hw))

/-- The value of `Padic.modPowTwoEquiv` on the class of `p ^ n * m` for an integer `m` prime to
`p`, whose residue class modulo `p` is the unit `w`. -/
theorem modPowTwoEquiv_mk_of_val_eq (hp2 : p ≠ 2) {x : ℚ_[p]ˣ} (n : ℕ) (m : ℤ) (w : (ZMod p)ˣ)
    (hx : (x : ℚ_[p]) = p ^ n * m) (hw : (w : ZMod p) = m) :
    modPowTwoEquiv p hp2 x = (.ofAdd (n : ZMod 2), (w : Units.ModPow (ZMod p) 2)) :=
  modPowTwoEquiv_mk_of_eq_pow_mul hp2 n m w (by simp [hx]) (by simp [hw])

/-- The value of `Padic.modPowTwoEquiv` on the class of `y ∈ ℤ_[p]` with `y ≡ p ^ n * m` modulo
`p ^ k`, `n < k`, for an integer `m` whose residue class modulo `p` is the unit `w`. -/
theorem modPowTwoEquiv_mk_of_toZModPow_eq (hp2 : p ≠ 2) {x : ℚ_[p]ˣ} (y : ℤ_[p]) (n k : ℕ)
    (m : ℤ) (w : (ZMod p)ˣ) (hnk : n < k) (hx : (x : ℚ_[p]) = y)
    (hy : PadicInt.toZModPow k y = p ^ n * m) (hw : (w : ZMod p) = m) :
    modPowTwoEquiv p hp2 x = (.ofAdd (n : ZMod 2), (w : Units.ModPow (ZMod p) 2)) := by
  obtain ⟨u, rfl, hu⟩ := PadicInt.exists_eq_pow_mul_of_toZModPow_eq hnk hy
  exact modPowTwoEquiv_mk_of_eq_pow_mul hp2 n u w (by simp [hx]) (by rw [hu, hw])

/-- For a monic quadratic `X ^ 2 + b X + c` over `ℚ_[p]` whose discriminant has odd valuation,
`u + w θ` is not a square in `ℚ_[p][X] ⧸ (X ^ 2 + b X + c)`, `θ` the root, if `u - w b / 2` lies in
`ℤ_[p]` with a nonsquare residue: `4 u - 2 b w = α ^ 2 + (b ^ 2 - 4 c) β ^ 2`
(`AdjoinRoot.exists_eq_sq_add_mul_sq_of_isSquare`) would make `‖(b ^ 2 - 4 c) β ^ 2‖ < 1`
(`Padic.norm_mul_sq_lt_one_of_odd_valuation`), so the residue of `u - w b / 2` would be a
square. -/
theorem not_isSquare_adjoinRoot_of_odd_valuation {f : ℚ_[p][X]} {b c u w : ℚ_[p]}
    (hf : f = X ^ 2 + C b * X + C c) (hD : Odd (b ^ 2 - 4 * c).valuation) {v : ℤ_[p]}
    (hv : (v : ℚ_[p]) = u - w * b / 2) (hsq : ¬ IsSquare (PadicInt.toZMod v)) :
    ¬ IsSquare (AdjoinRoot.of f u + AdjoinRoot.of f w * AdjoinRoot.root f) := by
  intro h
  obtain ⟨α, β, h, -⟩ := AdjoinRoot.exists_eq_sq_add_mul_sq_of_isSquare hf h
  have e : (v : ℚ_[p]) = (α / 2) ^ 2 + (b ^ 2 - 4 * c) * (β / 2) ^ 2 := by
    rw [hv]
    linear_combination h / 4
  exact hsq (PadicInt.isSquare_toZMod_of_coe_eq_sq_add
    (norm_mul_sq_lt_one_of_odd_valuation hD (e ▸ v.2)) e)

/-- A monic quadratic over `ℚ_[p]` whose discriminant has odd valuation is irreducible: the
discriminant is not a square (`Padic.even_valuation_of_isSquare`). -/
theorem irreducible_X_sq_add_C_mul_X_add_C_of_odd_valuation {b c : ℚ_[p]}
    (hD : Odd (b ^ 2 - 4 * c).valuation) : Irreducible (X ^ 2 + C b * X + C c) :=
  irreducible_X_sq_add_C_mul_X_add_C_of_not_isSquare fun h ↦
    Int.not_even_iff_odd.mpr hD (even_valuation_of_isSquare h)

/-- `ℚ_[p]ˣ/(ℚ_[p]ˣ)²` is finite, of order `8` for `p = 2` (`Padic.modPowTwoEquivZModEight`) and
`4` for odd `p` (`Padic.modPowTwoEquiv`). -/
instance finite_modPow_two : Finite (Units.ModPow ℚ_[p] 2) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · exact .of_equiv _ modPowTwoEquivZModEight.symm.toEquiv
  · exact .of_equiv _ (modPowTwoEquiv p hp2).symm.toEquiv

variable (p)

/-- **Square classes of `ℚ_[p]`** for odd `p` as `(ℤ / 2)²`: the valuation modulo `2`, and `0` or
`1` as the unit part is a square modulo `p` or not (`Padic.modPowTwoEquiv`, then
`FiniteField.modPowTwoEquivZModTwo`). -/
noncomputable def modPowTwoEquivZModTwo (hp2 : p ≠ 2) :
    Units.ModPow ℚ_[p] 2 ≃* Multiplicative (ZMod 2 × ZMod 2) :=
  ((modPowTwoEquiv p hp2).trans ((MulEquiv.refl _).prodCongr
    (FiniteField.modPowTwoEquivZModTwo (ZMod p) (by rwa [ZMod.ringChar_zmod_n])))).trans
      (MulEquiv.prodMultiplicative _ _).symm

/-- The coordinates under `Padic.modPowTwoEquivZModTwo` of the square class of a `p`-adic integer
with residue `z ≠ 0` modulo `p ^ 2` (`Padic.modPowTwoEquivZModTwo_mk_of_toZModPow_two_eq`): of a
unit with residue `z` if `p ∤ z`, otherwise of `p` times a unit with residue `z / p`. It is
computable, so that `decide` evaluates it. -/
def modPowTwoCoords (z : ZMod (p ^ 2)) : ZMod 2 × ZMod 2 :=
  if z.val % p = 0 then (1, if IsSquare ((z.val / p : ℕ) : ZMod p) then 0 else 1)
  else (0, if IsSquare (z.val : ZMod p) then 0 else 1)

variable {p}

/-- The value of `Padic.modPowTwoEquivZModTwo` on the class of `y ∈ ℤ_[p]` with `y ≡ p ^ n * m`
modulo `p ^ k`, `n < k`, for an integer `m` prime to `p`. -/
theorem modPowTwoEquivZModTwo_mk_of_toZModPow_eq (hp2 : p ≠ 2) {x : ℚ_[p]ˣ} (y : ℤ_[p])
    (n k : ℕ) (m : ℤ) (hnk : n < k) (hx : (x : ℚ_[p]) = y)
    (hy : PadicInt.toZModPow k y = p ^ n * m) (hm : (m : ZMod p) ≠ 0) :
    modPowTwoEquivZModTwo p hp2 x =
      .ofAdd ((n : ZMod 2), if IsSquare (m : ZMod p) then 0 else 1) := by
  rw [modPowTwoEquivZModTwo, MulEquiv.trans_apply, MulEquiv.trans_apply,
    modPowTwoEquiv_mk_of_toZModPow_eq hp2 y n k m (.mk0 _ hm) hnk hx hy rfl,
    MulEquiv.prodCongr_apply, FiniteField.modPowTwoEquivZModTwo_mk]
  rfl

-- `p ^ 2 ∤ y`: the class of `y` from its residue modulo `p ^ 2`.
private theorem modPowTwoEquivZModTwo_mk_of_toZModPow_two_eq' (hp2 : p ≠ 2) {x : ℚ_[p]ˣ}
    (y : ℤ_[p]) (hx : (x : ℚ_[p]) = y) {z : ZMod (p ^ 2)} (hy : PadicInt.toZModPow 2 y = z)
    (hz : z ≠ 0) : modPowTwoEquivZModTwo p hp2 x = .ofAdd (modPowTwoCoords p z) := by
  have hp := (Fact.out : p.Prime)
  rcases eq_or_ne (z.val % p) 0 with h | h
  · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hz ((ZMod.val_eq_zero z).mp (by simpa using hm))
    have hmp : m < p := Nat.lt_of_mul_lt_mul_left (by rw [← hm, ← sq]; exact ZMod.val_lt z)
    simp only [modPowTwoCoords, h, ↓reduceIte]
    rw [hm, Nat.mul_div_cancel_left m hp.pos,
      modPowTwoEquivZModTwo_mk_of_toZModPow_eq hp2 y 1 2 m one_lt_two hx
        (by rw [hy, ← ZMod.natCast_zmod_val z, hm]; push_cast; ring)
        (mod_cast fun h ↦ hm0 (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff m p).mp h) hmp))]
    simp
  · simp only [modPowTwoCoords, h, ↓reduceIte]
    rw [modPowTwoEquivZModTwo_mk_of_toZModPow_eq hp2 y 0 2 z.val two_pos hx (by simp [hy])
      (mod_cast mt (ZMod.natCast_eq_zero_iff _ p).mp (mt Nat.mod_eq_zero_of_dvd h))]
    simp

/-- The value of `Padic.modPowTwoEquivZModTwo` on the class of `c ^ 2 * y` for `y ∈ ℤ_[p]` with
residue `z ≠ 0` modulo `p ^ 2`: the coordinates `Padic.modPowTwoCoords p z`, which `decide`
evaluates. -/
theorem modPowTwoEquivZModTwo_mk_of_toZModPow_two_eq (hp2 : p ≠ 2) {x : ℚ_[p]ˣ} {c : ℚ_[p]}
    (y : ℤ_[p]) (hx : (x : ℚ_[p]) = c ^ 2 * y) {z : ZMod (p ^ 2)}
    (hy : PadicInt.toZModPow 2 y = z) (hz : z ≠ 0) :
    modPowTwoEquivZModTwo p hp2 x = .ofAdd (modPowTwoCoords p z) := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hx
  have hy0 : (y : ℚ_[p]) ≠ 0 := fun h ↦ x.ne_zero (by rw [hx, h, mul_zero])
  rw [(Units.ModPow.mk_eq_mk_iff (u := x) (v := .mk0 _ hy0) (n := 2)).mpr
    ⟨.mk0 c hc, Units.ext (by simp [hx, mul_comm])⟩,
    modPowTwoEquivZModTwo_mk_of_toZModPow_two_eq' hp2 y (Units.val_mk0 hy0) hy hz]

/-- An element `x = c ^ 2 * y` of `ℚ_[p]`, `c ≠ 0`, for `y ∈ ℤ_[p]` with residue `z ≠ 0` modulo
`p ^ 2`, is a square if and only if `Padic.modPowTwoCoords p z = 0`, which `decide` checks. -/
theorem isSquare_iff_modPowTwoCoords_eq_zero (hp2 : p ≠ 2) {x c : ℚ_[p]} (hc : c ≠ 0)
    (y : ℤ_[p]) (hx : x = c ^ 2 * y) {z : ZMod (p ^ 2)} (hy : PadicInt.toZModPow 2 y = z)
    (hz : z ≠ 0) : IsSquare x ↔ modPowTwoCoords p z = 0 := by
  have hy0 : (y : ℚ_[p]) ≠ 0 := fun h0 ↦ hz (by rw [← hy, PadicInt.coe_eq_zero.mp h0, map_zero])
  rw [← Units.val_mk0 (hx ▸ mul_ne_zero (pow_ne_zero 2 hc) hy0 : x ≠ 0),
    ← Units.ModPow.mk_eq_one_iff_isSquare, ← (modPowTwoEquivZModTwo p hp2).map_eq_one_iff,
    modPowTwoEquivZModTwo_mk_of_toZModPow_two_eq hp2 y (by rw [Units.val_mk0, hx]) hy hz]
  exact ofAdd_eq_one

end Padic

end
