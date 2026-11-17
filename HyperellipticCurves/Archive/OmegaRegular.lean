/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.DiskExpand
public import HyperellipticCurves.Archive.SecondKind

import HyperellipticCurves.Archive.Mathlib.Algebra.QuadraticAlgebra.Defs
import HyperellipticCurves.Archive.Mathlib.FieldTheory.RatFunc.Degree

/-!
# Regularity of `ω′` (blueprint `thm:omega-prime-global` clause (c))

`ChabautyColeman.omegaPrime_regular` assembles the `ω′`-regularity from the second-kind
classification: if the global differential numerator
`φ_i = y·∑_j N_{ij}·D(ζ_j)` (`ChabautyColeman.globOmega`) is holomorphic at every affine
place and at infinity, then it is a polynomial `P(x)` with `deg P < g`
(`ChabautyColeman.exists_regular_numerator_of_holomorphic`), and by the disk-expansion
transport (`ChabautyColeman.globExpand_globOmega`) the per-disk `ω′`-series satisfies
`b·η·ω′_i = P(a+z)` — the numerator of `ω′_i` as a regular differential.

The two holomorphy inputs (`haffine`, `hinfty`) are the two halves of the holomorphy
verification, and both are discharged here from *denominator-clearing certificates*:

* `ChabautyColeman.two_mul_y_mul_deriv_toHypField` — the algebraic heart:
  `2·y·D(P + Q·y) = (2Q′f + Qf′) + 2P′·y` is **integral**; the `y`-prefactor in `φ_i`
  cancels the only poles the derivation `d/dx` creates (at the Weierstrass points).
* `ChabautyColeman.valuation_globOmega_le_one` — the **affine half**: given clearing
  certificates for two auxiliary-point configurations computing the same `φ_i` (clause
  (a) at the generic point) whose denominators satisfy a Bézout relation, `v(φ_i) ≤ 1`
  at *every* affine place: at each place one configuration has unit denominators
  (`ChabautyColeman.valuation_eq_one_or_of_bezout`, the nonarchimedean pigeonhole), and
  there the bound is pure valuation algebra
  (`ChabautyColeman.valuation_y_mul_sum_deriv_le_one`).
* `ChabautyColeman.toHypField_mul_globOmega` — the **infinite half**: `(s²·s_N)·2·φ_i`
  is integral with explicit numerator, so `inftyOrd φ_i` is a certificate-degree
  computation via `ChabautyColeman.inftyOrd_toHypField` and
  `ChabautyColeman.inftyOrd_mul`.

Combining with `ChabautyColeman.regularDiffBasis` (a unit coordinate determinant, the
good-position Jacobian condition) yields the basis half of clause (c).

The main theorems do not depend on this file: the trace-form route, run per disk in
`HyperellipticCurves.Log.Trace.TraceKz`, exhibits the regular numerator outright, so no
holomorphy verification is needed. The per-disk expansion identity
`ChabautyColeman.omegaPrime_taylor`, which takes the polynomial numerator as a hypothesis and
therefore does not care where it came from, lives with the transport it belongs to, in
`HyperellipticCurves.Archive.DiskExpand`.
-/

@[expose] public section

open Polynomial IsDedekindDomain
open scoped PowerSeries
open scoped WithZero

namespace ChabautyColeman

section YDeriv

open HypField

variable {K : Type*} [Field K] [NeZero (2 : K)] {f : K[X]} [Fact (Odd f.natDegree)]

/-- **The `y`-scaled derivative is integral**: `2·y·D(P + Q·y) = (2Q′f + Qf′) + 2P′·y`.
The only poles the curve derivation `D = d/dx` creates on an integral function sit at the
Weierstrass points (from `dy/dx = f′/(2y)`), and the `y`-prefactor cancels them — this is
why the differential numerators `φ_i = y·∑_j N_{ij}·D(ζ_j)` can be holomorphic. -/
theorem two_mul_y_mul_deriv_toHypField (hf0 : f ≠ 0) (w : HypRing K f) :
    2 * (y f * HypField.deriv (HypRing.toHypField f w))
      = HypRing.toHypField f
          ⟨2 * w.im.derivative * f + w.im * f.derivative, 2 * w.re.derivative⟩ := by
  have hfR : algebraMap K[X] (RatFunc K) f ≠ 0 :=
    fun h ↦ hf0 (RatFunc.algebraMap_injective K (h.trans (map_zero _).symm))
  -- the coefficient of `y` in `D(y)` doubles to `f′/f`
  have hT : 2 * algebraMap (RatFunc K) (HypField K f)
        (algebraMap K[X] (RatFunc K) f.derivative / (2 * algebraMap K[X] (RatFunc K) f))
        * algebraMap K[X] (HypField K f) f
      = algebraMap K[X] (HypField K f) f.derivative := by
    rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f),
      IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f)]
    rw [show (2 : HypField K f) = algebraMap (RatFunc K) (HypField K f) 2 from
      (map_ofNat _ 2).symm, ← map_mul, ← map_mul]
    congr 1
    have h2R : (2 : RatFunc K) ≠ 0 := two_ne_zero
    field_simp
  rw [HypRing.toHypField_apply, HypRing.toHypField_apply, deriv_add, deriv_mul hf0,
    deriv_algebraMap_polynomial, deriv_algebraMap_polynomial, deriv_y]
  simp only [map_add, map_mul, map_ofNat]
  linear_combination (2 * algebraMap K[X] (HypField K f) w.im.derivative
      + 2 * algebraMap K[X] (HypField K f) w.im
        * algebraMap (RatFunc K) (HypField K f)
            (algebraMap K[X] (RatFunc K) f.derivative
              / (2 * algebraMap K[X] (RatFunc K) f))) * (y_sq (f := f))
    + algebraMap K[X] (HypField K f) w.im * hT

/-- **Denominator-clearing representation of the differential numerator** (for the
infinite place): `(s²·sN)·2·φ_i` is integral, with explicit numerator. Its
`ChabautyColeman.inftyOrd` is therefore computable from certificate degrees via
`ChabautyColeman.inftyOrd_toHypField` and `ChabautyColeman.inftyOrd_mul`, which reduces
the `hinfty` hypothesis of `ChabautyColeman.omegaPrime_regular` to a polynomial degree
count on the clearing certificates. -/
theorem toHypField_mul_globOmega (uτ vτ : K[X]) (a xQ yQ m₀ : K)
    (d : CantorCertData (HypField K f))
    (N : Fin uτ.natDegree → Fin uτ.natDegree → HypField K f) (i : Fin uτ.natDegree)
    {s sN : HypRing K f} {w wN : Fin uτ.natDegree → HypRing K f}
    (hw : ∀ j, HypRing.toHypField f s * globZeta f uτ vτ a xQ yQ m₀ d j
      = HypRing.toHypField f (w j))
    (hwN : ∀ j, HypRing.toHypField f sN * N i j = HypRing.toHypField f (wN j))
    (hf0 : f ≠ 0) :
    HypRing.toHypField f (s * s * sN) * (2 * globOmega f uτ vτ a xQ yQ m₀ d N i)
      = HypRing.toHypField f (∑ j, wN j
          * (s * ⟨2 * (w j).im.derivative * f + (w j).im * f.derivative, 2 * (w j).re.derivative⟩
            - (⟨2 * s.im.derivative * f + s.im * f.derivative,
                2 * s.re.derivative⟩ : HypRing K f) * w j)) := by
  rw [globOmega, map_sum]
  rw [show HypRing.toHypField f (s * s * sN)
        * (2 * (y f * ∑ j, N i j * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)))
      = ∑ j, HypRing.toHypField f (s * s * sN)
          * (N i j * (2 * (y f * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)))) from by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- the per-coordinate cleared identity
  have hD := congrArg (fun g ↦ 2 * (y f * HypField.deriv g)) (hw j)
  simp only [deriv_mul hf0] at hD
  rw [show 2 * (y f * (HypField.deriv (HypRing.toHypField f s) * globZeta f uτ vτ a xQ yQ m₀ d j
        + HypRing.toHypField f s
          * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)))
      = 2 * (y f * HypField.deriv (HypRing.toHypField f s))
          * globZeta f uτ vτ a xQ yQ m₀ d j
        + HypRing.toHypField f s
          * (2 * (y f * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j))) from by ring,
    two_mul_y_mul_deriv_toHypField hf0 s, two_mul_y_mul_deriv_toHypField hf0 (w j)] at hD
  simp only [map_mul, map_sub]
  linear_combination (HypRing.toHypField f s * HypRing.toHypField f (wN j)) * hD
    + (HypRing.toHypField f s * HypRing.toHypField f s
        * (2 * (y f * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)))) * (hwN j)
    - HypRing.toHypField f
        (⟨2 * s.im.derivative * f + s.im * f.derivative, 2 * s.re.derivative⟩ : HypRing K f)
      * HypRing.toHypField f (wN j) * (hw j)

end YDeriv

section InftyCount

open RatFunc HypField

variable {K : Type*} [Field K] [NeZero (2 : K)] {f : K[X]} [Fact (Odd f.natDegree)]

/-- **The infinite-place count for the global differential numerator** (`hinfty` of
`ChabautyColeman.omegaPrime_regular`): if all chart coordinates `ζ_j` and all entries
of the row `N_{i·}` are bounded at the infinite place, then
`ord_∞(φ_i) ≥ -(2g-2)` for `φ_i = y·∑_j N_{ij}·D(ζ_j)`: the derivative gains order
`≥ 3` at infinity (`ChabautyColeman.RatFunc.IntDegreeLE.derivative_of_nonpos` on the
`x`-part), which exactly compensates the pole `-(2g+1)` of `y`. -/
theorem neg_le_inftyOrd_globOmega (uτ vτ : K[X]) (a xQ yQ m₀ : K)
    (d : CantorCertData (HypField K f))
    (N : Fin uτ.natDegree → Fin uτ.natDegree → HypField K f) (i : Fin uτ.natDegree)
    (hg : 1 ≤ genus f)
    (hζ : ∀ j, 0 ≤ inftyOrd (globZeta f uτ vτ a xQ yQ m₀ d j))
    (hN : ∀ j, 0 ≤ inftyOrd (N i j)) :
    -(2 * (genus f : ℤ) - 2) ≤ inftyOrd (globOmega f uτ vτ a xQ yQ m₀ d N i) := by
  have hfd : f.natDegree = 2 * genus f + 1 := (two_mul_genus_add_one Fact.out).symm
  have hf0 : f ≠ 0 := fun h ↦ by rw [h] at hfd; simp at hfd
  -- the `y`-coefficient of `D(y)` has degree `≤ -1`
  have hquot : (algebraMap K[X] (RatFunc K) (Polynomial.derivative f)
      / (2 * algebraMap K[X] (RatFunc K) f)).IntDegreeLE (-1) := by
    rcases eq_or_ne (Polynomial.derivative f) 0 with h0 | h0
    · rw [h0, map_zero, zero_div]
      exact intDegreeLE_zero _
    have h2 : (2 : K[X]) ≠ 0 := by
      rw [← map_ofNat Polynomial.C 2]
      exact Polynomial.C_ne_zero.mpr two_ne_zero
    have h2f : (2 : RatFunc K) * algebraMap K[X] (RatFunc K) f
        = algebraMap K[X] (RatFunc K) (2 * f) := by
      rw [map_mul, map_ofNat]
    refine .inr ?_
    rw [h2f, RatFunc.intDegree_div (algebraMap_ne_zero h0)
      (algebraMap_ne_zero (mul_ne_zero h2 hf0)), RatFunc.intDegree_polynomial,
      RatFunc.intDegree_polynomial, natDegree_mul h2 hf0]
    have hd := Polynomial.natDegree_derivative_le f
    simp only [natDegree_ofNat, zero_add]
    lia
  -- per-coordinate bounds on the summands
  have hterm : ∀ j : Fin uτ.natDegree,
      ((N i j * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)).re).IntDegreeLE (-2)
        ∧ ((N i j * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)).im).IntDegreeLE
            (-(genus f : ℤ) - 2) := by
    intro j
    obtain ⟨hζre, hζim⟩ := intDegreeLE_re_im_of_inftyOrd_nonneg (hζ j)
    obtain ⟨hNre, hNim⟩ := intDegreeLE_re_im_of_inftyOrd_nonneg (hN j)
    have hDre : ((HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)).re).IntDegreeLE
        (-2) := by
      rw [re_deriv]
      exact hζre.derivative_of_nonpos
    have hDim : ((HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)).im).IntDegreeLE
        (-(genus f : ℤ) - 2) := by
      rw [im_deriv]
      exact (hζim.derivative.of_le (by lia)).add ((hζim.mul hquot).of_le (by lia))
    refine ⟨?_, ?_⟩
    · rw [QuadraticAlgebra.re_mul]
      exact ((hNre.mul hDre).of_le (by
        lia)).add
        ((((intDegreeLE_algebraMap f).mul hNim).mul hDim).of_le (by push_cast [hfd]; lia))
    · rw [QuadraticAlgebra.im_mul]
      refine (((hNre.mul hDim).of_le (by lia)).add ((hNim.mul hDre).of_le (by lia))).add ?_
      simpa using intDegreeLE_zero (-(genus f : ℤ) - 2)
  -- assemble via the component computation
  rw [globOmega]
  refine neg_le_inftyOrd (r := (genus f : ℤ) - 1) (i := -2) ?_ ?_ (by
    lia)
    (by push_cast [hfd]; lia) (by lia)
  · rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
    simp only [zero_mul, mul_one, zero_add]
    rw [QuadraticAlgebra.im_sum]
    exact ((intDegreeLE_algebraMap f).mul (IntDegreeLE.sum fun j _ ↦ (hterm j).2)).of_le
      (by push_cast [hfd]; lia)
  · rw [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
    simp only [zero_mul, one_mul, zero_add, add_zero]
    rw [QuadraticAlgebra.re_sum]
    exact IntDegreeLE.sum fun j _ ↦ (hterm j).1

end InftyCount

section Holomorphy

open HypField IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NeZero (2 : K)] {f : K[X]} [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]

/-- The valuation of the image of a coordinate-ring element is at most `1`. -/
theorem valuation_toHypField_le_one (v : HeightOneSpectrum (HypRing K f))
    (w : HypRing K f) : v.valuation (HypField K f) (HypRing.toHypField f w) ≤ 1 :=
  valuation_le_one v w

/-- In a linearly ordered monoid: two subunit factors with unit product are units. -/
private theorem eq_one_of_mul_eq_one {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : ℤᵐ⁰) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a

/-- The valuation of `2` at every place is `1` (it is a unit of the coordinate ring). -/
theorem valuation_two_eq_one (v : HeightOneSpectrum (HypRing K f)) :
    v.valuation (HypField K f) (2 : HypField K f) = 1 := by
  have hprod : (2 : HypRing K f) * algebraMap K (HypRing K f) 2⁻¹ = 1 := by
    rw [show (2 : HypRing K f) = algebraMap K (HypRing K f) 2 from (map_ofNat _ 2).symm,
      ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have h2 : (2 : HypField K f) = HypRing.toHypField f 2 := (map_ofNat _ 2).symm
  rw [h2]
  refine eq_one_of_mul_eq_one (valuation_toHypField_le_one v 2)
    (valuation_toHypField_le_one v (algebraMap K (HypRing K f) 2⁻¹)) ?_
  rw [← map_mul, ← map_mul, hprod, map_one]
  exact map_one _

/-- **The per-place holomorphy bound** (affine half, one configuration): if the
denominators `s`, `sN` clearing the chart coordinates `ζ` and the matrix row `N` are
units at the place `v`, then `v(y·∑_j N_j·D(ζ_j)) ≤ 1`. The proof is purely algebraic:
`2·y·D` maps integral functions to integral functions
(`ChabautyColeman.two_mul_y_mul_deriv_toHypField` — the `y`-prefactor cancels the
Weierstrass poles of `d/dx`), and clearing denominators reduces every ingredient to an
integral one. -/
theorem valuation_y_mul_sum_deriv_le_one (v : HeightOneSpectrum (HypRing K f))
    {ι : Type*} [Fintype ι] (ζ N : ι → HypField K f) (s sN : HypRing K f)
    (w wN : ι → HypRing K f)
    (hs : v.valuation (HypField K f) (HypRing.toHypField f s) = 1)
    (hsN : v.valuation (HypField K f) (HypRing.toHypField f sN) = 1)
    (hw : ∀ j, HypRing.toHypField f s * ζ j = HypRing.toHypField f (w j))
    (hwN : ∀ j, HypRing.toHypField f sN * N j = HypRing.toHypField f (wN j))
    (hf0 : f ≠ 0) :
    v.valuation (HypField K f) (y f * ∑ j, N j * HypField.deriv (ζ j)) ≤ 1 := by
  set val := v.valuation (HypField K f) with hval
  have h2 : val 2 = 1 := valuation_two_eq_one v
  have hζle : ∀ j, val (ζ j) ≤ 1 := fun j ↦ by
    have h := congrArg val (hw j)
    rw [map_mul, hs, one_mul] at h
    rw [h]
    exact valuation_toHypField_le_one v _
  have hNle : ∀ j, val (N j) ≤ 1 := fun j ↦ by
    have h := congrArg val (hwN j)
    rw [map_mul, hsN, one_mul] at h
    rw [h]
    exact valuation_toHypField_le_one v _
  have hyD : ∀ j, val (y f * HypField.deriv (ζ j)) ≤ 1 := fun j ↦ by
    -- differentiate the clearing identity and rescale by `2y`
    have hD := congrArg (fun g ↦ 2 * (y f * HypField.deriv g)) (hw j)
    simp only [deriv_mul hf0] at hD
    rw [show 2 * (y f * (HypField.deriv (HypRing.toHypField f s) * ζ j
          + HypRing.toHypField f s * HypField.deriv (ζ j)))
        = 2 * (y f * HypField.deriv (HypRing.toHypField f s)) * ζ j
          + HypRing.toHypField f s * (2 * (y f * HypField.deriv (ζ j))) from by ring,
      two_mul_y_mul_deriv_toHypField hf0 s, two_mul_y_mul_deriv_toHypField hf0 (w j)]
      at hD
    have hkey : HypRing.toHypField f s * (2 * (y f * HypField.deriv (ζ j)))
        = HypRing.toHypField f
            ⟨2 * (w j).im.derivative * f + (w j).im * f.derivative, 2 * (w j).re.derivative⟩
          - HypRing.toHypField f
              ⟨2 * s.im.derivative * f + s.im * f.derivative, 2 * s.re.derivative⟩
            * ζ j := by linear_combination hD
    have hb : val (2 * (y f * HypField.deriv (ζ j))) ≤ 1 := by
      have h1 := congrArg val hkey
      rw [map_mul, hs, one_mul] at h1
      rw [h1]
      refine val.map_sub_le (valuation_toHypField_le_one v _) ?_
      rw [map_mul]
      exact mul_le_one' (valuation_toHypField_le_one v _) (hζle j)
    rwa [map_mul, h2, one_mul] at hb
  rw [Finset.mul_sum]
  refine val.map_sum_le fun j _ ↦ ?_
  rw [show y f * (N j * HypField.deriv (ζ j)) = N j * (y f * HypField.deriv (ζ j)) from by
    ring, map_mul]
  exact mul_le_one' (hNle j) (hyD j)

/-- **Bézout coverage**: a Bézout relation between two coordinate-ring elements makes at
least one of them a unit at every place (the nonarchimedean pigeonhole for the two bad
loci). -/
theorem valuation_eq_one_or_of_bezout (v : HeightOneSpectrum (HypRing K f))
    {α β s s' : HypRing K f} (hbez : α * s + β * s' = 1) :
    v.valuation (HypField K f) (HypRing.toHypField f s) = 1
      ∨ v.valuation (HypField K f) (HypRing.toHypField f s') = 1 := by
  set val := v.valuation (HypField K f) with hval
  by_contra! hcon
  obtain ⟨h1, h2⟩ := hcon
  have hs1 : val (HypRing.toHypField f s) < 1 :=
    lt_of_le_of_ne (valuation_toHypField_le_one v s) h1
  have hs2 : val (HypRing.toHypField f s') < 1 :=
    lt_of_le_of_ne (valuation_toHypField_le_one v s') h2
  have hone := congrArg val (congrArg (HypRing.toHypField f) hbez)
  rw [map_one, map_one, map_add, map_mul, map_mul] at hone
  have hlt : val (HypRing.toHypField f α * HypRing.toHypField f s)
      ⊔ val (HypRing.toHypField f β * HypRing.toHypField f s') < 1 := by
    rw [map_mul, map_mul]
    refine max_lt ?_ ?_
    · rw [mul_comm]
      calc val (HypRing.toHypField f s) * val (HypRing.toHypField f α)
          ≤ val (HypRing.toHypField f s) * 1 :=
            mul_le_mul_right (valuation_toHypField_le_one v α) _
        _ = val (HypRing.toHypField f s) := mul_one _
        _ < 1 := hs1
    · rw [mul_comm]
      calc val (HypRing.toHypField f s') * val (HypRing.toHypField f β)
          ≤ val (HypRing.toHypField f s') * 1 :=
            mul_le_mul_right (valuation_toHypField_le_one v β) _
        _ = val (HypRing.toHypField f s') := mul_one _
        _ < 1 := hs2
  exact absurd (hone.symm.trans_lt (lt_of_le_of_lt (val.map_add _ _) hlt)) (lt_irrefl 1)

/-- **The affine half of the holomorphy verification**: the global differential
numerator `φ_i = y·∑_j N_{ij}·D(ζ_j)` has valuation `≤ 1` at *every* affine place, given
denominator-clearing certificates for two auxiliary-point configurations computing the
same `φ_i` (`hindep`, clause (a) at the generic point) whose denominators satisfy a
Bézout relation (`hbez` — the two bad loci are disjoint). At each place at least one
configuration has unit denominators (`ChabautyColeman.valuation_eq_one_or_of_bezout`),
and there the bound is the algebraic integrality of `2·y·D`
(`ChabautyColeman.valuation_y_mul_sum_deriv_le_one`). This discharges the `haffine`
hypothesis of `ChabautyColeman.omegaPrime_regular`. -/
theorem valuation_globOmega_le_one (uτ vτ : K[X]) (a xQ yQ m₀ xQ' yQ' m₀' : K)
    (d d' : CantorCertData (HypField K f))
    (N : Fin uτ.natDegree → Fin uτ.natDegree → HypField K f) (i : Fin uτ.natDegree)
    (hindep : globOmega f uτ vτ a xQ yQ m₀ d N i = globOmega f uτ vτ a xQ' yQ' m₀' d' N i)
    {s sN s' sN' : HypRing K f} {w wN w' wN' : Fin uτ.natDegree → HypRing K f}
    (hw : ∀ j, HypRing.toHypField f s * globZeta f uτ vτ a xQ yQ m₀ d j
      = HypRing.toHypField f (w j))
    (hwN : ∀ j, HypRing.toHypField f sN * N i j = HypRing.toHypField f (wN j))
    (hw' : ∀ j, HypRing.toHypField f s' * globZeta f uτ vτ a xQ' yQ' m₀' d' j
      = HypRing.toHypField f (w' j))
    (hwN' : ∀ j, HypRing.toHypField f sN' * N i j = HypRing.toHypField f (wN' j))
    {α β : HypRing K f} (hbez : α * (s * sN) + β * (s' * sN') = 1) (hf0 : f ≠ 0)
    (v : HeightOneSpectrum (HypRing K f)) :
    v.valuation (HypField K f) (globOmega f uτ vτ a xQ yQ m₀ d N i) ≤ 1 := by
  have hsplit : ∀ {u u' : HypRing K f},
      v.valuation (HypField K f) (HypRing.toHypField f (u * u')) = 1
        → v.valuation (HypField K f) (HypRing.toHypField f u) = 1
          ∧ v.valuation (HypField K f) (HypRing.toHypField f u') = 1 := by
    intro u u' h
    rw [map_mul, map_mul] at h
    exact ⟨eq_one_of_mul_eq_one (valuation_toHypField_le_one v u)
        (valuation_toHypField_le_one v u') h,
      eq_one_of_mul_eq_one (valuation_toHypField_le_one v u')
        (valuation_toHypField_le_one v u) (by rwa [mul_comm] at h)⟩
  rcases valuation_eq_one_or_of_bezout v hbez with h | h
  · obtain ⟨hs, hsN⟩ := hsplit h
    rw [globOmega]
    exact valuation_y_mul_sum_deriv_le_one v _ _ s sN w wN hs hsN hw hwN hf0
  · obtain ⟨hs, hsN⟩ := hsplit h
    rw [hindep, globOmega]
    exact valuation_y_mul_sum_deriv_le_one v _ _ s' sN' w' wN' hs hsN hw' hwN' hf0

end Holomorphy

section GlobAuxIndep

open HypField

variable {K : Type*} [Field K] [CharZero K] {f : K[X]} [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]
  {uτ vτ : K[X]} {a b xQ yQ m₀ xQ' yQ' m₀' : K} {d d' : CantorCertData (HypField K f)}

/-- **Auxiliary-point independence of the global chart** (blueprint
`thm:omega-prime-global` clause (a), at the generic point): two runs of the global
pipeline through different auxiliary points `Q`, `Q′` (with their certificate packs)
produce the *same* Mumford datum over the function field — the auxiliary classes cancel
(`ChabautyColeman.mk0_pair_mul_mk0_pair_chain`) and reduced representatives of a class
are unique (`ChabautyColeman.cantorPipeline_eq_cantorPipeline_of_mk0_eq`). -/
theorem globPipeline_eq_of_aux (hf : f.Monic)
    (hsep : a ≠ xQ) (hsep' : a ≠ xQ')
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hm₀' : m₀' * (a - xQ') = -b - yQ')
    (hb : b ^ 2 = f.eval a) (hyQ : yQ ^ 2 = f.eval xQ) (hyQ' : yQ' ^ 2 = f.eval xQ')
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map (algebraMap K (HypField K f)))
      (globConfig f uτ vτ a xQ yQ m₀) d uτ.natDegree)
    (hcerts' : IsPipelineCerts (f.map (algebraMap K (HypField K f)))
      (globConfig f uτ vτ a xQ' yQ' m₀') d' uτ.natDegree) :
    globPipeline f uτ vτ a xQ yQ m₀ d = globPipeline f uτ vτ a xQ' yQ' m₀' d' := by
  classical
  have hεinj : Function.Injective (algebraMap K (HypField K f)) :=
    (algebraMap K (HypField K f)).injective
  -- ambient instances for the mapped curve polynomial over the function field
  have hchH : CharZero (HypField K f) := charZero_of_injective_algebraMap hεinj
  have h2H : NeZero (2 : HypField K f) := ⟨by norm_num⟩
  have hOddH : Fact (Odd ((f.map (algebraMap K (HypField K f))).natDegree)) := ⟨by
    rw [hf.natDegree_map]
    exact Fact.out⟩
  have hSqH : Fact (Squarefree (f.map (algebraMap K (HypField K f)))) :=
    ⟨((PerfectField.separable_iff_squarefree.mpr Fact.out).map).squarefree⟩
  -- the input facts
  have hu₁ : (globU₁ f xQ).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₁' : (globU₁ f xQ').Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂ : ((uτ.map (algebraMap K (HypField K f)))).Monic := huτ.map _
  have hu₃ : (globU₃ f a xQ).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hu₃' : (globU₃ f a xQ').Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have heval : ∀ {c c' : K}, c' ^ 2 = f.eval c →
      (algebraMap K (HypField K f) c') ^ 2
        = (f.map (algebraMap K (HypField K f))).eval (algebraMap K (HypField K f) c) :=
    fun {c c'} h ↦ by rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, ← map_pow, h]
  have hd₁ := globPair_dvd f hyQ
  have hd₁' := globPair_dvd f hyQ'
  have hd₂ : uτ.map (algebraMap K (HypField K f))
      ∣ (vτ.map (algebraMap K (HypField K f))) ^ 2
        - f.map (algebraMap K (HypField K f)) := map_dvd_sq_sub _ hdvdτ
  have hd₃ := globPair₃_dvd f hsep hm₀ hb hyQ
  have hd₃' := globPair₃_dvd f hsep' hm₀' hb hyQ'
  have hgF : 2 * uτ.natDegree < (f.map (algebraMap K (HypField K f))).natDegree := by
    rwa [hf.natDegree_map]
  -- the class products of the two input triples agree: the auxiliary classes cancel
  have hxne : ∀ c : K, HypField.x f ≠ algebraMap K (HypField K f) c := fun c h ↦
    algebraMap_sub_x_ne_zero f c (by rw [← h, sub_self])
  have hmPQ : ∀ {xq yq : K}, globSlope f xq yq
      * (algebraMap K (HypField K f) xq - HypField.x f)
      = -(algebraMap K (HypField K f) yq) - y f := fun {xq yq} ↦ by
    have h := globSlope_spec f xq yq
    rwa [map_neg] at h
  have hm₀K : ∀ {xq yq mq : K}, mq * (a - xq) = -b - yq →
      algebraMap K (HypField K f) mq
          * (algebraMap K (HypField K f) a - algebraMap K (HypField K f) xq)
        = -(algebraMap K (HypField K f) b) - algebraMap K (HypField K f) yq :=
    fun {xq yq mq} h ↦ by rw [← map_sub, ← map_mul, h, map_sub, map_neg]
  have hchain := mk0_pair_mul_mk0_pair_chain (f := f.map (algebraMap K (HypField K f)))
    (hxne xQ) (fun h ↦ hsep (hεinj h).symm) hmPQ (hm₀K hm₀) (y_sq_eval f) (heval hyQ)
    (heval hb)
  have hchain' := mk0_pair_mul_mk0_pair_chain (f := f.map (algebraMap K (HypField K f)))
    (hxne xQ') (fun h ↦ hsep' (hεinj h).symm) hmPQ (hm₀K hm₀') (y_sq_eval f) (heval hyQ')
    (heval hb)
  -- rewrite the constant pairs into split point-pair shape
  have hU₃eq : ∀ c : K, globU₃ f a c
      = (X - C (algebraMap K (HypField K f) c)) * (X - C (algebraMap K (HypField K f) a)) :=
    fun c ↦ by simp [globU₃]
  have hV₃eq : ∀ c c' c'' : K, globV₃ f c c' c''
      = pairV (algebraMap K (HypField K f) c) (algebraMap K (HypField K f) c')
          (algebraMap K (HypField K f) c'') := fun c c' c'' ↦ pairV_map _ c c' c''
  rw [globPipeline, globPipeline]
  refine cantorPipeline_eq_cantorPipeline_of_mk0_eq hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hu₁' hd₁'
    hu₂ hd₂ hu₃' hd₃' hcerts hcerts' hgF ?_
  simp only [globConfig_u₁, globConfig_v₁, globConfig_u₂, globConfig_v₂, globConfig_u₃,
    globConfig_v₃, hU₃eq, hV₃eq]
  calc _ = _ := mul_right_comm _ _ _
    _ = _ := congrArg
        (· * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap K (HypField K f)))
            (uτ.map (algebraMap K (HypField K f))) (vτ.map (algebraMap K (HypField K f))),
          mumfordIdeal_mem_nonZeroDivisors _ hu₂.ne_zero _⟩)
        (hchain.trans hchain'.symm)
    _ = _ := (mul_right_comm _ _ _).symm

/-- Auxiliary-point independence of the global chart coordinates. -/
theorem globZeta_eq_of_aux (hf : f.Monic)
    (hsep : a ≠ xQ) (hsep' : a ≠ xQ')
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hm₀' : m₀' * (a - xQ') = -b - yQ')
    (hb : b ^ 2 = f.eval a) (hyQ : yQ ^ 2 = f.eval xQ) (hyQ' : yQ' ^ 2 = f.eval xQ')
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map (algebraMap K (HypField K f)))
      (globConfig f uτ vτ a xQ yQ m₀) d uτ.natDegree)
    (hcerts' : IsPipelineCerts (f.map (algebraMap K (HypField K f)))
      (globConfig f uτ vτ a xQ' yQ' m₀') d' uτ.natDegree) :
    globZeta f uτ vτ a xQ yQ m₀ d = globZeta f uτ vτ a xQ' yQ' m₀' d' := by
  funext j
  rw [globZeta, globZeta, globPipeline_eq_of_aux hf hsep hsep' hm₀ hm₀' hb hyQ hyQ' huτ
    hdvdτ hgτ hcerts hcerts']

/-- **Auxiliary-point independence of the differential numerators** (clause (a) at the
generic point): this discharges the `hindep` hypothesis of
`ChabautyColeman.valuation_globOmega_le_one`. -/
theorem globOmega_eq_of_aux (hf : f.Monic)
    (hsep : a ≠ xQ) (hsep' : a ≠ xQ')
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hm₀' : m₀' * (a - xQ') = -b - yQ')
    (hb : b ^ 2 = f.eval a) (hyQ : yQ ^ 2 = f.eval xQ) (hyQ' : yQ' ^ 2 = f.eval xQ')
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map (algebraMap K (HypField K f)))
      (globConfig f uτ vτ a xQ yQ m₀) d uτ.natDegree)
    (hcerts' : IsPipelineCerts (f.map (algebraMap K (HypField K f)))
      (globConfig f uτ vτ a xQ' yQ' m₀') d' uτ.natDegree)
    (N : Fin uτ.natDegree → Fin uτ.natDegree → HypField K f) (i : Fin uτ.natDegree) :
    globOmega f uτ vτ a xQ yQ m₀ d N i = globOmega f uτ vτ a xQ' yQ' m₀' d' N i := by
  rw [globOmega, globOmega, globZeta_eq_of_aux hf hsep hsep' hm₀ hm₀' hb hyQ hyQ' huτ
    hdvdτ hgτ hcerts hcerts']

end GlobAuxIndep

section Regular

open HypField

variable {O : Type*} [CommRing O] [Nontrivial O] {K : Type*} [Field K] [CharZero K]
  [NeZero (2 : K)] {ψ : O →+* K}
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [Fact (Odd (f.map ψ).natDegree)] [Fact (Squarefree (f.map ψ))]

/-- **Regularity of `ω′`** (blueprint `thm:omega-prime-global` clause (c)): if the global
differential numerator `φ_i = y·∑_j N_{ij}·D(ζ_j)` is holomorphic at every affine place
(`haffine`) and at infinity (`hinfty`) — the two halves of the holomorphy verification — then
by the second-kind classification `ChabautyColeman.exists_regular_numerator_of_holomorphic` it
is a polynomial `P(x)` of degree `< g`, and `ChabautyColeman.omegaPrime_taylor` supplies the
per-disk expansion identity. -/
theorem omegaPrime_regular
    (dg : CantorCertData (HypField K (f.map ψ)))
    (hbK : (ψ b) ^ 2 = (f.map ψ).eval (ψ a)) (hfaK : (f.map ψ).eval (ψ a) ≠ 0)
    (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hcertsg : IsPipelineCerts ((f.map ψ).map (algebraMap K (HypField K (f.map ψ))))
      (globConfig (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀)) dg
      uτ.natDegree)
    (ΦK : FormalGroupLaw K (Fin (uτ.map ψ).natDegree))
    (ζK : Fin (uτ.map ψ).natDegree → K⟦X⟧)
    (hζK : ∀ j : Fin uτ.natDegree, ζK ⟨j, lt_of_lt_of_eq j.2 (huτ.natDegree_map ψ).symm⟩
        = PowerSeries.map ψ (phiZeta f a b xQ yQ m m₀ uτ vτ d j))
    (N : Fin (uτ.map ψ).natDegree → Fin (uτ.map ψ).natDegree → HypField K (f.map ψ))
    (hN : ∀ i j, globExpand (f.map ψ) (ψ a) (ψ b) hbK hfaK (N i j)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (MvPowerSeries.subst ζK (ΦK.diffMatrix⁻¹ i j)))
    (i : Fin (uτ.map ψ).natDegree)
    (haffine : ∀ v : HeightOneSpectrum (HypRing K (f.map ψ)), v.valuation (HypField K (f.map ψ))
        (globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg N i) ≤ 1)
    (hinfty : -(2 * (genus (f.map ψ) : ℤ) - 2)
      ≤ inftyOrd (globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg N i)) :
    ∃ P : K[X], P.degree < genus (f.map ψ)
      ∧ globOmega (f.map ψ) (uτ.map ψ) (vτ.map ψ) (ψ a) (ψ xQ) (ψ yQ) (ψ m₀) dg N i
          = HypRing.toHypField (f.map ψ) ⟨P, 0⟩
      ∧ PowerSeries.C (ψ b) * diskSeriesGeneric (f.map ψ) (ψ a) * omegaPrime ΦK ζK i
          = (taylor (ψ a) P : K⟦X⟧) := by
  obtain ⟨P, hPdeg, hPeq⟩ :=
    exists_regular_numerator_of_holomorphic (f := f.map ψ) _ haffine hinfty
  exact ⟨P, hPdeg, hPeq, omegaPrime_taylor dg hbK hfaK hf hsep hm hm₀ hb hfa h2 hyQ huτ hdvdτ
    hgτ hcerts hcertsg ΦK ζK hζK N hN i hPeq⟩

end Regular

end ChabautyColeman

end
