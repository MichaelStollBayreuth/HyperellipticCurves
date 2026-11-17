/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.RatFuncDerivative
public import HyperellipticCurves.Curve.HypRing
public import Mathlib.RingTheory.Derivation.Basic

import HyperellipticCurves.Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The curve derivation on the function field

The derivation `D = d/dx` on the function field `F_K = K(x)[Y]/(Y² - f)` of the
hyperelliptic curve `y² = f(x)`: it extends the formal derivative on `K(x)`
(`RatFunc.derivative`) by `D(y) = f′/(2f)·y`, obtained by differentiating the curve
relation `y² = f`. Componentwise, `D(a + b·y) = a′ + (b′ + b·f′/(2f))·y`
(`ChabautyColeman.HypField.deriv`).

`D` is the derivation with respect to which a rational differential `ω = φ·dx` is
compared against `dx/y`: for a function `g` on the curve, `dg = D(g)·dx`. It is additive
(`ChabautyColeman.HypField.deriv_add`), satisfies the Leibniz rule
(`ChabautyColeman.HypField.deriv_mul`), restricts to `d/dx` on `K(x)`
(`ChabautyColeman.HypField.deriv_algebraMap`), and satisfies `2y·D(y) = f′`
(`ChabautyColeman.HypField.two_mul_y_mul_deriv_y`). Over a base field in which `2` is
invertible it is packaged as a bundled `Derivation`
(`ChabautyColeman.HypField.derivation`).

This is the derivative half of the global realization of the differentials `ω′` of
`thm:omega-prime-global` clause (c): `ω′_i = φ_i·dx/y` with `φ_i = y·∑_j N_{ij}(ζ)·D(ζ_j)`
for the global chart coordinates `ζ` (`ChabautyColeman.globZeta`); the assembled
trace-form route consumes the derivation through `Derivation.dotDer` and the trace-form
differential `ChabautyColeman.traceDiff` (`HyperellipticCurves.Curve.TraceDiff`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

namespace HypField

variable {K : Type*} [Field K] {f : K[X]}

/-- The **curve derivation** `D` on the function field of `y² = f(x)`: extends `d/dx` on
`K(x)` by `D(y) = f′/(2f)·y` (differentiate `y² = f`). Componentwise:
`D(a + b·y) = a′ + (b′ + b·f′/(2f))·y`. -/
noncomputable def deriv (z : HypField K f) : HypField K f :=
  ⟨RatFunc.derivative z.re,
   RatFunc.derivative z.im + z.im * (algebraMap K[X] (RatFunc K) (Polynomial.derivative f)
     / (2 * algebraMap K[X] (RatFunc K) f))⟩

@[simp] theorem re_deriv (z : HypField K f) : (deriv z).re = RatFunc.derivative z.re := rfl

@[simp] theorem im_deriv (z : HypField K f) :
    (deriv z).im = RatFunc.derivative z.im
      + z.im * (algebraMap K[X] (RatFunc K) (Polynomial.derivative f)
        / (2 * algebraMap K[X] (RatFunc K) f)) := rfl

/-- The curve derivation is additive. -/
theorem deriv_add (z w : HypField K f) : deriv (z + w) = deriv z + deriv w := by
  ext
  · simp [RatFunc.derivative_add]
  · simp [RatFunc.derivative_add]
    ring

/-- The curve derivation restricts to `d/dx` on the rational-function subfield. -/
@[simp]
theorem deriv_algebraMap (r : RatFunc K) :
    deriv (algebraMap (RatFunc K) (HypField K f) r)
      = algebraMap (RatFunc K) (HypField K f) (RatFunc.derivative r) := by
  rw [← QuadraticAlgebra.C_eq_algebraMap]
  ext
  · simp [deriv]
  · simp [deriv]

/-- The curve derivation extends the polynomial derivative on `K[x]`. -/
@[simp]
theorem deriv_algebraMap_polynomial (p : K[X]) :
    deriv (algebraMap K[X] (HypField K f) p)
      = algebraMap K[X] (HypField K f) (Polynomial.derivative p) := by
  rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f),
    IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f), deriv_algebraMap,
    RatFunc.derivative_algebraMap]

/-- The curve derivation kills the constants of the coordinate ring. -/
@[simp]
theorem deriv_toHypField_C (c : K) :
    deriv (HypRing.toHypField f (⟨Polynomial.C c, 0⟩ : HypRing K f)) = 0 := by
  rw [HypRing.toHypField_apply]
  simp

/-- The curve derivation kills the constants of the base field. -/
@[simp]
theorem deriv_algebraMap_baseField (c : K) : deriv (algebraMap K (HypField K f) c) = 0 := by
  ext <;> simp [deriv]

/-- The curve derivation is `K`-linear. -/
theorem deriv_smul (c : K) (z : HypField K f) : deriv (c • z) = c • deriv z := by
  ext
  · simp [RatFunc.derivative_smul]
  · simp only [im_deriv, QuadraticAlgebra.im_smul, RatFunc.derivative_smul, smul_add,
      smul_mul_assoc]

/-- The curve derivation as a `K`-linear map; `HypField.derivation` bundles it further. -/
noncomputable def derivₗ : HypField K f →ₗ[K] HypField K f where
  toFun := deriv
  map_add' := deriv_add
  map_smul' := deriv_smul

@[simp] theorem derivₗ_apply (z : HypField K f) : derivₗ z = deriv z := rfl

/-- `D(y) = f′/(2f)·y`. -/
theorem deriv_y :
    deriv (y f) = algebraMap (RatFunc K) (HypField K f)
      (algebraMap K[X] (RatFunc K) (Polynomial.derivative f)
        / (2 * algebraMap K[X] (RatFunc K) f)) * y f := by
  rw [← QuadraticAlgebra.C_eq_algebraMap]
  ext
  · simp [deriv, y]
  · simp [deriv, y]

variable [NeZero (2 : K)]

/-- **Leibniz rule** for the curve derivation (`f ≠ 0`, `2 ≠ 0`). -/
theorem deriv_mul (hf : f ≠ 0) (z w : HypField K f) :
    deriv (z * w) = deriv z * w + z * deriv w := by
  have h2 : (2 : RatFunc K) ≠ 0 := two_ne_zero
  have hfz : algebraMap K[X] (RatFunc K) f ≠ 0 := RatFunc.algebraMap_ne_zero hf
  ext
  · simp only [deriv, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add, RatFunc.derivative_add, RatFunc.derivative_mul,
      RatFunc.derivative_algebraMap, RatFunc.derivative_zero]
    field_simp
    ring
  · simp only [deriv, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.im_add, RatFunc.derivative_add, RatFunc.derivative_mul,
      RatFunc.derivative_algebraMap, RatFunc.derivative_zero]
    field_simp
    ring

/-- The **curve derivation** `D = d/dx`, bundled as a `K`-derivation of the function field.
This is the form the trace-form differential `ChabautyColeman.traceDiff` consumes: bundling
supplies the Leibniz rule for the coefficientwise extension `Derivation.dotDer` for free. -/
noncomputable def derivation (hf : f ≠ 0) : Derivation K (HypField K f) (HypField K f) :=
  Derivation.mk' derivₗ fun z w ↦ by simp only [derivₗ_apply, deriv_mul hf, smul_eq_mul]; ring

@[simp] theorem derivation_apply (hf : f ≠ 0) (z : HypField K f) : derivation hf z = deriv z := rfl

/-- Cleared form: `2y·D(y) = f′` (differentiating `y² = f`). -/
theorem two_mul_y_mul_deriv_y (hf : f ≠ 0) :
    2 * y f * deriv (y f) = algebraMap K[X] (HypField K f) (Polynomial.derivative f) := by
  have h2 : (2 : RatFunc K) ≠ 0 := two_ne_zero
  have hfz : algebraMap K[X] (RatFunc K) f ≠ 0 := RatFunc.algebraMap_ne_zero hf
  rw [deriv_y, show 2 * y f * (algebraMap (RatFunc K) (HypField K f)
        (algebraMap K[X] (RatFunc K) (Polynomial.derivative f)
          / (2 * algebraMap K[X] (RatFunc K) f)) * y f)
      = algebraMap (RatFunc K) (HypField K f)
        (algebraMap K[X] (RatFunc K) (Polynomial.derivative f)
          / (2 * algebraMap K[X] (RatFunc K) f)) * (2 * y f ^ 2) from by ring,
    y_sq, IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f),
    IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f) (Polynomial.derivative f),
    show (2 : HypField K f) = algebraMap (RatFunc K) (HypField K f) 2 from (map_ofNat _ 2).symm,
    ← map_mul, ← map_mul]
  refine congrArg _ ?_
  field_simp

end HypField

end ChabautyColeman

end
