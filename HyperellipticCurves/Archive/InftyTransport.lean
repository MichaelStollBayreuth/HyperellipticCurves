/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.ForMathlib.QuadraticAlgebra
public import HyperellipticCurves.Archive.ForMathlib.RatFunc
public import HyperellipticCurves.Archive.GlobalChart
public import HyperellipticCurves.Archive.SecondKind
public import HyperellipticCurves.Disks.ChartsInf
public import HyperellipticCurves.Series.SqrtSeries

/-!
# The infinity-chart expansion of the function field

The infinite-place expansion `E_∞` of the place-by-place holomorphy verification for
`thm:omega-prime-global` clause (c), where it serves to bound `ord_∞` of the chart
coordinates. The main theorems do not depend on this file: the trace-form route needs no such
bound. Note that the `∞`-disk work of chapter 4 uses the independent parametrization of
`HyperellipticCurves.Disks.ChartsInf` (the contraction fixed point of `u = z²·(reverse f)(u)`
over the base ring), not this function-field substitution `x = t⁻²`.

The infinite-place analogue of the disk-expansion homomorphism
`ChabautyColeman.globExpand`: the ring homomorphism
`E_∞ = ChabautyColeman.infExpand : F_K →+* Frac(K⟦t⟧)` given by the infinity-chart
substitution `x = t⁻²`, `y = t^(-(2g+1))·η`, where `η = √((reverse f)(t²))` is a unit
power series (`ChabautyColeman.infEta`, via `ChabautyColeman.sqrtSeries`; no Hensel lemma
is needed since `x = t⁻²` is exact). The on-curve identity `(infY)² = f(t⁻²)` is the
reverse-polynomial relation `f(t⁻²)·(t²)^(deg f) = (reverse f)(t²)`
(`ChabautyColeman.infPolyHom_mul_pow`, from `ChabautyColeman.eval_map_inv_mul_pow`),
which also gives injectivity of the base substitution on `K(x)`
(`ChabautyColeman.infPolyHom_injective`), so `E_∞` is constructed via
`IsFractionRing.lift` and `QuadraticAlgebra.liftRingHom` exactly like the disk
expansion.

The **order-parity transfer** (`ChabautyColeman.inftyOrd_nonneg_of_infExpand_mem`):
if `E_∞(ξ)` is a power series (no pole in `t`), then `ord_∞(ξ) ≥ 0`. Componentwise
(`ChabautyColeman.intDegreeLE_re_im_of_infExpand_eq`): clearing denominators turns the
expansion into an identity of power series whose two summands have `t`-orders of
opposite parity — the `K(x)`-part has even order (`ChabautyColeman.infRatHom_mul_eq`,
with unit series `ChabautyColeman.infEta2`), the `y`-part has odd order
(`deg f = 2g + 1`) — so no cancellation can hide a pole, and
`PowerSeries.order_add_of_order_ne` bounds both components. This is the interface for
discharging the boundedness inputs `hζ`, `hN` of
`ChabautyColeman.neg_le_inftyOrd_globOmega`; what remains is the `t`-integrality of the
`E_∞`-image of the pipeline output.
-/

@[expose] public section

open Polynomial PowerSeries

namespace ChabautyColeman

section InfExpansion

variable {K : Type*} [Field K]

/-- The reversed curve polynomial evaluated at `t²`: the square of the `y`-normalization
on the infinity chart, `(reverse f)(t²) ∈ K⟦t⟧` (a unit series for monic `f`). -/
noncomputable def infEta2 (f : K[X]) : PowerSeries K :=
  Polynomial.eval₂ (PowerSeries.C : K →+* PowerSeries K) (PowerSeries.X ^ 2) (reverse f)

theorem constantCoeff_infEta2 (f : K[X]) :
    PowerSeries.constantCoeff (infEta2 f) = f.leadingCoeff := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.X ^ 2 : PowerSeries K) = 0 := by simp
  rw [infEta2, Polynomial.hom_eval₂, h0, Polynomial.eval₂_at_zero, RingHom.comp_apply,
    PowerSeries.constantCoeff_C, coeff_zero_reverse]

/-- The square-root series `η` of `(reverse f)(t²)`, normalized by `η(0) = 1`
(for `f` monic). -/
noncomputable def infEta (f : K[X]) : PowerSeries K :=
  sqrtSeries (infEta2 f) 1 (2 : K)⁻¹

/-- The evaluation `p(x) ↦ p(t⁻²)` of polynomial functions into the Laurent-series field
`Frac(K⟦t⟧)` — the infinity-chart substitution `x = t⁻²`. -/
noncomputable def infPolyHom (K : Type*) [Field K] :
    K[X] →+* FractionRing (PowerSeries K) :=
  Polynomial.eval₂RingHom
    ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
      (PowerSeries.C : K →+* PowerSeries K))
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.X ^ 2))⁻¹

theorem reverse_map_powerSeriesC (p : K[X]) :
    reverse (p.map (PowerSeries.C : K →+* PowerSeries K))
      = (reverse p).map (PowerSeries.C : K →+* PowerSeries K) := by
  rw [reverse, reverse, natDegree_map_eq_of_injective PowerSeries.C_injective,
    reflect_map]

/-- `p(t⁻²)·(t²)^(deg p)` is the (image of the) reversed polynomial at `t²`. -/
theorem infPolyHom_mul_pow (p : K[X]) :
    infPolyHom K p
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (PowerSeries.X ^ 2) ^ p.natDegree
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (infEta2 p) := by
  have hX2 : (PowerSeries.X ^ 2 : PowerSeries K) ≠ 0 := pow_ne_zero 2 PowerSeries.X_ne_zero
  have h := eval_map_inv_mul_pow (K := FractionRing (PowerSeries K))
    (p.map (PowerSeries.C : K →+* PowerSeries K)) hX2
  rw [natDegree_map_eq_of_injective PowerSeries.C_injective, Polynomial.map_map,
    reverse_map_powerSeriesC, eval_map, eval_map] at h
  rw [infPolyHom, coe_eval₂RingHom, infEta2]
  exact h

theorem infPolyHom_injective : Function.Injective (infPolyHom K) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp ↦ ?_
  by_contra hp0
  have h := infPolyHom_mul_pow p
  rw [hp, zero_mul] at h
  have h0 : infEta2 p = 0 :=
    IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
      (h.symm.trans (map_zero _).symm)
  have hc := constantCoeff_infEta2 p
  rw [h0, map_zero] at hc
  exact hp0 (leadingCoeff_eq_zero.mp hc.symm)

/-- The infinity-chart substitution on the rational-function field: `r(x) ↦ r(t⁻²)`. -/
noncomputable def infRatHom (K : Type*) [Field K] :
    RatFunc K →+* FractionRing (PowerSeries K) :=
  IsFractionRing.lift (infPolyHom_injective (K := K))

theorem infRatHom_algebraMap (p : K[X]) :
    infRatHom K (algebraMap K[X] (RatFunc K) p) = infPolyHom K p :=
  IsFractionRing.lift_algebraMap _ p

variable (f : K[X])

/-- The infinity-chart image of `y`: `t^(-(2g+1))·η` with `η = √((reverse f)(t²))`. -/
noncomputable def infY : FractionRing (PowerSeries K) :=
  algebraMap (PowerSeries K) _ (infEta f)
    * (algebraMap (PowerSeries K) _ (PowerSeries.X ^ f.natDegree))⁻¹

variable [NeZero (2 : K)]

theorem infEta_sq (hf : f.Monic) : infEta f ^ 2 = infEta2 f := by
  refine sqrtSeries_sq _ (by rw [one_pow, constantCoeff_infEta2, hf.leadingCoeff]) ?_
  rw [mul_one, mul_inv_cancel₀ (two_ne_zero (α := K))]

/-- The square-root certificate for the infinity expansion: `(infY)²` is the image
of `f`. -/
theorem infY_sq (hf : f.Monic) :
    infY f ^ 2 = infRatHom K (algebraMap K[X] (RatFunc K) f)
      + infRatHom K (0 : RatFunc K)
        * infY f := by
  rw [map_zero, zero_mul, add_zero, infRatHom_algebraMap]
  have hXd : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (PowerSeries.X ^ f.natDegree) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hmul := infPolyHom_mul_pow f
  have h2 := congrArg (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))
    (infEta_sq f hf)
  rw [map_pow] at h2
  have hX2 : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (((PowerSeries.X : PowerSeries K) ^ 2) ^ f.natDegree) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)]
    exact pow_ne_zero _ (pow_ne_zero _ PowerSeries.X_ne_zero)
  rw [infY, mul_pow, h2, inv_pow, ← map_pow,
    show ((PowerSeries.X : PowerSeries K) ^ f.natDegree) ^ 2
      = (PowerSeries.X ^ 2) ^ f.natDegree from by ring, ← hmul, ← map_pow, mul_assoc,
    mul_inv_cancel₀ hX2, mul_one]

/-- **The infinity-chart expansion homomorphism** `E_∞ : F_K →+* Frac(K⟦t⟧)`: the
substitution `x = t⁻²`, `y = t^(-(2g+1))·η` with `η = √((reverse f)(t²))` (the on-curve
identity is the reverse-polynomial relation `f(t⁻²)·t^(2·deg f) = (reverse f)(t²)`).
The infinite-place analogue of the disk expansion `ChabautyColeman.globExpand`. -/
noncomputable def infExpand (hf : f.Monic) :
    HypField K f →+* FractionRing (PowerSeries K) :=
  QuadraticAlgebra.liftRingHom (infRatHom K) (infY f) (infY_sq f hf)

theorem infExpand_comp_algebraMap (hf : f.Monic) :
    (infExpand f hf).comp (algebraMap (RatFunc K) (HypField K f)) = infRatHom K :=
  QuadraticAlgebra.liftRingHom_comp_algebraMap _ _ _

theorem infExpand_y (hf : f.Monic) : infExpand f hf (HypField.y f) = infY f :=
  QuadraticAlgebra.liftRingHom_omega _ _ _

theorem infExpand_x (hf : f.Monic) :
    infExpand f hf (HypField.x f)
      = (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.X ^ 2))⁻¹ := by
  rw [HypField.x, IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f),
    show infExpand f hf ((algebraMap (RatFunc K) (HypField K f))
        (algebraMap K[X] (RatFunc K) X))
      = infRatHom K (algebraMap K[X] (RatFunc K) X) from
      RingHom.congr_fun (infExpand_comp_algebraMap f hf) _,
    infRatHom_algebraMap, infPolyHom, coe_eval₂RingHom, Polynomial.eval₂_X]

end InfExpansion

/-! ### Order-parity transfer: integrality of the expansion bounds the infinite order -/

section InfOrder

variable {K : Type*} [Field K]

theorem isUnit_infEta2 {p : K[X]} (hp : p ≠ 0) : IsUnit (infEta2 p) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_infEta2]
  exact isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)

/-- Cleared form of the infinity-chart image of a rational function:
`r(t⁻²)·(v·t^(2a)) = u·t^(2b)` with `u, v` unit series and `b - a = -deg r`. -/
theorem infRatHom_mul_eq (r : RatFunc K) :
    infRatHom K r
        * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (infEta2 r.denom * PowerSeries.X ^ (2 * r.num.natDegree))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (infEta2 r.num * PowerSeries.X ^ (2 * r.denom.natDegree)) := by
  have hcross : infRatHom K r * infPolyHom K r.denom = infPolyHom K r.num := by
    rw [← infRatHom_algebraMap, ← infRatHom_algebraMap, ← map_mul]
    congr 1
    exact ((div_eq_iff (RatFunc.algebraMap_ne_zero r.denom_ne_zero)).mp
      (RatFunc.num_div_denom r)).symm
  have hnum := infPolyHom_mul_pow r.num
  have hden := infPolyHom_mul_pow r.denom
  have e1 : ∀ n : ℕ, algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (PowerSeries.X ^ (2 * n))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.X ^ 2) ^ n := by
    intro n
    rw [← map_pow, ← pow_mul]
  rw [map_mul, map_mul, e1, e1, ← hnum, ← hden]
  linear_combination (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (PowerSeries.X ^ 2) ^ r.num.natDegree
    * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
        (PowerSeries.X ^ 2) ^ r.denom.natDegree) * hcross

theorem isUnit_infEta (f : K[X]) : IsUnit (infEta f) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, infEta, constantCoeff_sqrtSeries]
  exact isUnit_one

/-- Clearing the `t`-power from the infinity-chart image of `y`. -/
theorem infY_mul_eq (f : K[X]) :
    infY f * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
        (PowerSeries.X ^ f.natDegree)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (infEta f) := by
  have hX : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (PowerSeries.X ^ f.natDegree) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) _)]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  rw [infY, mul_assoc, inv_mul_cancel₀ hX, mul_one]

open RatFunc in
/-- **The order-parity transfer** (componentwise): a function-field element
whose infinity-chart expansion is integral (a power series, no pole in `t`) has both
`K(x)`-components bounded at the infinite place: `intDegree ≤ 0` for the `x`-part and
`intDegree ≤ -(g+1)` for the `y`-part. The two cleared summands have `t`-orders of
opposite parity (`deg f = 2g + 1` is odd), so no cancellation can hide a pole. -/
theorem intDegreeLE_re_im_of_infExpand_eq {f : K[X]} (hf : f.Monic)
    (hodd : Odd f.natDegree) [NeZero (2 : K)] {ξ : HypField K f} {w : PowerSeries K}
    (h : infExpand f hf ξ
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) w) :
    ξ.re.IntDegreeLE 0 ∧ ξ.im.IntDegreeLE (-(genus f : ℤ) - 1) := by
  have hinj := IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
  have hg := two_mul_genus_add_one hodd
  have happ : infRatHom K ξ.re + infRatHom K ξ.im * infY f
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) w := h
  rcases eq_or_ne ξ.im 0 with him | him
  · refine ⟨?_, .inl him⟩
    rcases eq_or_ne ξ.re 0 with hre | hre
    · exact .inl hre
    rw [him, map_zero, zero_mul, add_zero] at happ
    have hcl := infRatHom_mul_eq ξ.re
    rw [happ, ← map_mul] at hcl
    have hK := hinj hcl
    have horder := congrArg PowerSeries.order hK
    rw [PowerSeries.order_mul, PowerSeries.order_mul, PowerSeries.order_mul,
      order_zero_of_isUnit (isUnit_infEta2 (num_ne_zero hre)),
      order_zero_of_isUnit (isUnit_infEta2 ξ.re.denom_ne_zero),
      PowerSeries.order_X_pow, PowerSeries.order_X_pow, zero_add, zero_add] at horder
    have hle : ((2 * ξ.re.num.natDegree : ℕ) : ℕ∞) ≤ (2 * ξ.re.denom.natDegree : ℕ) := by
      rw [← horder]
      exact le_add_self
    have hnat := Nat.cast_le.mp hle
    have hint : ξ.re.intDegree = (ξ.re.num.natDegree : ℤ) - ξ.re.denom.natDegree := rfl
    exact .inr (by lia)
  rcases eq_or_ne ξ.re 0 with hre | hre
  · refine ⟨.inl hre, ?_⟩
    rw [hre, map_zero, zero_add] at happ
    have hL : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
        (infEta2 ξ.im.num * PowerSeries.X ^ (2 * ξ.im.denom.natDegree) * infEta f
          + 0)
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (w * (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree)
              * PowerSeries.X ^ f.natDegree)) := by
      have hLg : infRatHom K ξ.im * algebraMap (PowerSeries K) (FractionRing
            (PowerSeries K)) (infEta2 ξ.im.denom
              * PowerSeries.X ^ (2 * ξ.im.num.natDegree))
            * (infY f * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (PowerSeries.X ^ f.natDegree))
          = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) w
            * (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
                (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree))
              * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
                  (PowerSeries.X ^ f.natDegree)) := by
        linear_combination (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree))
          * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (PowerSeries.X ^ f.natDegree)) * happ
      rw [infRatHom_mul_eq, infY_mul_eq] at hLg
      simp only [map_mul] at hLg
      simp only [map_mul, add_zero]
      linear_combination hLg
    have hK := hinj hL
    rw [add_zero] at hK
    have horder := congrArg PowerSeries.order hK
    simp only [PowerSeries.order_mul, PowerSeries.order_X_pow,
      order_zero_of_isUnit (isUnit_infEta2 (num_ne_zero him)),
      order_zero_of_isUnit (isUnit_infEta2 ξ.im.denom_ne_zero),
      order_zero_of_isUnit (isUnit_infEta f), zero_add, add_zero] at horder
    have hle : ((2 * ξ.im.num.natDegree : ℕ) : ℕ∞) + (f.natDegree : ℕ)
        ≤ ((2 * ξ.im.denom.natDegree : ℕ) : ℕ∞) := horder ▸ le_add_self
    have hnat : 2 * ξ.im.num.natDegree + f.natDegree ≤ 2 * ξ.im.denom.natDegree := by
      exact_mod_cast hle
    have hint : ξ.im.intDegree = (ξ.im.num.natDegree : ℤ) - ξ.im.denom.natDegree := rfl
    exact .inr (by lia)
  -- both components nonzero: the parity argument
  have hL : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (infEta2 ξ.re.num * PowerSeries.X ^ (2 * ξ.re.denom.natDegree)
          * (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree)
            * PowerSeries.X ^ f.natDegree)
        + infEta2 ξ.im.num * PowerSeries.X ^ (2 * ξ.im.denom.natDegree)
          * (infEta2 ξ.re.denom * PowerSeries.X ^ (2 * ξ.re.num.natDegree) * infEta f))
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (w * (infEta2 ξ.re.denom * PowerSeries.X ^ (2 * ξ.re.num.natDegree)
            * (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree)
              * PowerSeries.X ^ f.natDegree))) := by
    have hLg : infRatHom K ξ.re * algebraMap (PowerSeries K) (FractionRing
          (PowerSeries K)) (infEta2 ξ.re.denom
            * PowerSeries.X ^ (2 * ξ.re.num.natDegree))
          * (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree))
            * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
                (PowerSeries.X ^ f.natDegree))
        + infRatHom K ξ.im * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree))
          * (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (infEta2 ξ.re.denom * PowerSeries.X ^ (2 * ξ.re.num.natDegree))
            * (infY f * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
                (PowerSeries.X ^ f.natDegree)))
        = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) w
          * (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (infEta2 ξ.re.denom * PowerSeries.X ^ (2 * ξ.re.num.natDegree))
            * (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
                (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree))
              * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
                  (PowerSeries.X ^ f.natDegree))) := by
      linear_combination (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (infEta2 ξ.re.denom * PowerSeries.X ^ (2 * ξ.re.num.natDegree))
        * (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree))
          * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (PowerSeries.X ^ f.natDegree))) * happ
    rw [infRatHom_mul_eq, infRatHom_mul_eq, infY_mul_eq] at hLg
    simp only [map_mul] at hLg
    simp only [map_add, map_mul]
    linear_combination hLg
  have hK := hinj hL
  have ho₁ : PowerSeries.order (infEta2 ξ.re.num
      * PowerSeries.X ^ (2 * ξ.re.denom.natDegree)
      * (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree)
        * PowerSeries.X ^ f.natDegree))
      = ((2 * ξ.re.denom.natDegree : ℕ) : ℕ∞)
        + (((2 * ξ.im.num.natDegree : ℕ) : ℕ∞) + (f.natDegree : ℕ)) := by
    simp only [PowerSeries.order_mul, PowerSeries.order_X_pow,
      order_zero_of_isUnit (isUnit_infEta2 (num_ne_zero hre)),
      order_zero_of_isUnit (isUnit_infEta2 ξ.im.denom_ne_zero), zero_add]
  have ho₂ : PowerSeries.order (infEta2 ξ.im.num
      * PowerSeries.X ^ (2 * ξ.im.denom.natDegree)
      * (infEta2 ξ.re.denom * PowerSeries.X ^ (2 * ξ.re.num.natDegree) * infEta f))
      = ((2 * ξ.im.denom.natDegree : ℕ) : ℕ∞) + ((2 * ξ.re.num.natDegree : ℕ) : ℕ∞) := by
    simp only [PowerSeries.order_mul, PowerSeries.order_X_pow,
      order_zero_of_isUnit (isUnit_infEta2 (num_ne_zero him)),
      order_zero_of_isUnit (isUnit_infEta2 ξ.re.denom_ne_zero),
      order_zero_of_isUnit (isUnit_infEta f), zero_add, add_zero]
  have hne : PowerSeries.order (infEta2 ξ.re.num
      * PowerSeries.X ^ (2 * ξ.re.denom.natDegree)
      * (infEta2 ξ.im.denom * PowerSeries.X ^ (2 * ξ.im.num.natDegree)
        * PowerSeries.X ^ f.natDegree))
      ≠ PowerSeries.order (infEta2 ξ.im.num
        * PowerSeries.X ^ (2 * ξ.im.denom.natDegree)
        * (infEta2 ξ.re.denom * PowerSeries.X ^ (2 * ξ.re.num.natDegree) * infEta f)) := by
    rw [ho₁, ho₂]
    intro hEq
    have hEq' : 2 * ξ.re.denom.natDegree + (2 * ξ.im.num.natDegree + f.natDegree)
        = 2 * ξ.im.denom.natDegree + 2 * ξ.re.num.natDegree := by exact_mod_cast hEq
    obtain ⟨k, hk⟩ := hodd
    lia
  have horder := congrArg PowerSeries.order hK
  rw [PowerSeries.order_add_of_order_ne _ _ hne, ho₁, ho₂] at horder
  simp only [PowerSeries.order_mul, PowerSeries.order_X_pow,
    order_zero_of_isUnit (isUnit_infEta2 ξ.re.denom_ne_zero),
    order_zero_of_isUnit (isUnit_infEta2 ξ.im.denom_ne_zero), zero_add] at horder
  have hmin : ((2 * ξ.re.num.natDegree : ℕ) : ℕ∞)
        + (((2 * ξ.im.num.natDegree : ℕ) : ℕ∞) + (f.natDegree : ℕ))
      ≤ min (((2 * ξ.re.denom.natDegree : ℕ) : ℕ∞)
          + (((2 * ξ.im.num.natDegree : ℕ) : ℕ∞) + (f.natDegree : ℕ)))
        (((2 * ξ.im.denom.natDegree : ℕ) : ℕ∞) + ((2 * ξ.re.num.natDegree : ℕ) : ℕ∞)) :=
    horder ▸ le_add_self
  obtain ⟨h1, h2⟩ := le_min_iff.mp hmin
  have hn1 : 2 * ξ.re.num.natDegree + (2 * ξ.im.num.natDegree + f.natDegree)
      ≤ 2 * ξ.re.denom.natDegree + (2 * ξ.im.num.natDegree + f.natDegree) := by
    exact_mod_cast h1
  have hn2 : 2 * ξ.re.num.natDegree + (2 * ξ.im.num.natDegree + f.natDegree)
      ≤ 2 * ξ.im.denom.natDegree + 2 * ξ.re.num.natDegree := by
    exact_mod_cast h2
  have hire : ξ.re.intDegree = (ξ.re.num.natDegree : ℤ) - ξ.re.denom.natDegree := rfl
  have him' : ξ.im.intDegree = (ξ.im.num.natDegree : ℤ) - ξ.im.denom.natDegree := rfl
  exact ⟨.inr (by lia), .inr (by lia)⟩


open RatFunc in
/-- **Integrality of the infinity expansion gives boundedness at the infinite place**: if
`E_∞(ξ)` is a power series (no pole in the chart parameter `t`), then `ord_∞(ξ) ≥ 0`. This is
the interface for discharging the hypotheses `hζ`, `hN` of
`ChabautyColeman.neg_le_inftyOrd_globOmega`. -/
theorem inftyOrd_nonneg_of_infExpand_mem {f : K[X]} [Fact (Odd f.natDegree)]
    (hf : f.Monic) [NeZero (2 : K)] {ξ : HypField K f}
    (h : infExpand f hf ξ
      ∈ (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).range) :
    0 ≤ inftyOrd ξ := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨hre, him⟩ := intDegreeLE_re_im_of_infExpand_eq hf Fact.out hw.symm
  have hg := two_mul_genus_add_one (f := f) Fact.out
  have h0 := neg_le_inftyOrd hre him (by lia) (by lia) le_rfl
  simpa using h0

open RatFunc in
/-- **Unit-integrality of the infinity expansion pins the order**: if `E_∞(ξ)` is a power
series with nonzero constant term, then `ord_∞(ξ) = 0`. Both inequalities come from
`ChabautyColeman.inftyOrd_nonneg_of_infExpand_mem`, applied to `ξ` and to `ξ⁻¹` (the
series is a unit in `K⟦t⟧`). -/
theorem inftyOrd_eq_zero_of_infExpand_eq {f : K[X]} [Fact (Odd f.natDegree)]
    (hf : f.Monic) [NeZero (2 : K)] {ξ : HypField K f} {s : PowerSeries K}
    (h : infExpand f hf ξ = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) s)
    (h0 : PowerSeries.constantCoeff s ≠ 0) : inftyOrd ξ = 0 := by
  obtain ⟨u, rfl⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h0)
  have hξ0 : ξ ≠ 0 := by
    intro h'
    rw [h', map_zero] at h
    refine h0 ?_
    rw [show ((u : PowerSeries K)) = 0 from
      IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
        (by rw [← h, map_zero]), map_zero]
  have hinv : infExpand f hf ξ⁻¹ = algebraMap (PowerSeries K)
      (FractionRing (PowerSeries K)) ((u⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) := by
    rw [map_inv₀, h]
    exact (eq_inv_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])).symm
  have h1 := inftyOrd_nonneg_of_infExpand_mem hf ⟨u, h.symm⟩
  have h2 := inftyOrd_nonneg_of_infExpand_mem hf ⟨(u⁻¹ : (PowerSeries K)ˣ), hinv.symm⟩
  rw [inftyOrd_inv hξ0] at h2
  lia

end InfOrder

end ChabautyColeman

end
