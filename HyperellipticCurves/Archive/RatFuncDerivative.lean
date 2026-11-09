/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.ForMathlib.RatFunc
public import HyperellipticCurves.ForMathlib.FractionRingDerivative
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# The formal derivative of rational functions

The formal derivative on `K(x)` (`RatFunc.derivative`), the quotient-rule extension
`IsFractionRing.deriv` of `Polynomial.derivative`
(`HyperellipticCurves.ForMathlib.FractionRingDerivative`), together with the facts making it a
derivation extending the polynomial derivative:

* `RatFunc.derivative_div`: the quotient rule holds for *every* fraction representation;
* `RatFunc.derivative_algebraMap`: it extends `Polynomial.derivative`;
* `RatFunc.derivative_add`, `RatFunc.derivative_mul`: additivity and the Leibniz rule;
* `RatFunc.derivative_smul`: `K`-linearity;
* `RatFunc.derivative_eq`: its value on the reduced representation `x = num x / denom x`.

Intended for eventual upstreaming to Mathlib (which currently has no derivative on
`RatFunc`).
-/

@[expose] public section

open Polynomial

namespace RatFunc

variable {K : Type*} [Field K]

/-- Every rational function is a fraction of polynomials (with nonzero denominator), in
`∃`-form suitable for `obtain ⟨p, q, hq, rfl⟩` destructuring. -/
theorem exists_eq_div (x : RatFunc K) :
    ∃ p q : K[X], q ≠ 0 ∧ x = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q :=
  ⟨x.num, x.denom, x.denom_ne_zero, (num_div_denom x).symm⟩

/-- The formal derivative of a rational function: the quotient-rule extension
(`IsFractionRing.deriv`) of the polynomial derivative. The quotient rule for an arbitrary
representation is `RatFunc.derivative_div`; the derivation laws are `RatFunc.derivative_add`
and `RatFunc.derivative_mul`. -/
noncomputable def derivative (x : RatFunc K) : RatFunc K :=
  IsFractionRing.deriv (fun p : K[X] ↦ Polynomial.derivative p) x

/-- The quotient rule holds for every fraction representation, not just the reduced one. -/
theorem derivative_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    derivative (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q)
      = algebraMap K[X] (RatFunc K) (Polynomial.derivative p * q - p * Polynomial.derivative q)
        / algebraMap K[X] (RatFunc K) (q ^ 2) := by
  rw [derivative, IsFractionRing.deriv_div (fun _ _ ↦ Polynomial.derivative_mul) p hq,
    map_sub, map_mul, map_mul]

/-- The derivative of a rational function, on its reduced representation. -/
theorem derivative_eq (x : RatFunc K) :
    derivative x
      = algebraMap K[X] (RatFunc K)
          (Polynomial.derivative x.num * x.denom - x.num * Polynomial.derivative x.denom)
        / algebraMap K[X] (RatFunc K) (x.denom ^ 2) := by
  conv_lhs => rw [← num_div_denom x]
  rw [derivative_div _ x.denom_ne_zero]

/-- The derivative of a polynomial function is the polynomial derivative. -/
@[simp]
theorem derivative_algebraMap (p : K[X]) :
    derivative (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) (Polynomial.derivative p) :=
  IsFractionRing.deriv_algebraMap (fun _ _ ↦ Polynomial.derivative_mul) p

@[simp]
theorem derivative_zero : derivative (0 : RatFunc K) = 0 := by
  rw [← map_zero (algebraMap K[X] (RatFunc K)), derivative_algebraMap]
  simp

@[simp]
theorem derivative_one : derivative (1 : RatFunc K) = 0 := by
  rw [← map_one (algebraMap K[X] (RatFunc K)), derivative_algebraMap, Polynomial.derivative_one,
    map_zero]

@[simp]
theorem derivative_C (c : K) : derivative (C c) = 0 := by
  rw [← algebraMap_C, derivative_algebraMap, Polynomial.derivative_C, map_zero]

/-- Leibniz rule for the derivative of rational functions. -/
theorem derivative_mul (x y : RatFunc K) :
    derivative (x * y) = derivative x * y + x * derivative y :=
  IsFractionRing.deriv_mul (fun _ _ ↦ Polynomial.derivative_mul) x y

/-- Additivity of the derivative of rational functions. -/
theorem derivative_add (x y : RatFunc K) :
    derivative (x + y) = derivative x + derivative y :=
  IsFractionRing.deriv_add (fun _ _ ↦ Polynomial.derivative_add)
    (fun _ _ ↦ Polynomial.derivative_mul) x y

/-- The derivative is `K`-linear. -/
theorem derivative_smul (c : K) (x : RatFunc K) : derivative (c • x) = c • derivative x := by
  rw [smul_eq_C_mul, smul_eq_C_mul, derivative_mul, derivative_C, zero_mul, zero_add]

section IntDegree

/-- Numerator degree bound for the quotient rule: `deg(p′q - pq′) ≤ deg p + deg q - 1`
(in `ℤ`, valid also for constant `p` or `q`). -/
theorem _root_.Polynomial.natDegree_derivative_mul_sub_le {p q : K[X]}
    (h0 : Polynomial.derivative p * q - p * Polynomial.derivative q ≠ 0) :
    ((Polynomial.derivative p * q - p * Polynomial.derivative q).natDegree : ℤ)
      ≤ (p.natDegree : ℤ) + q.natDegree - 1 := by
  by_cases hp : p.natDegree = 0
  · obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hp
    have hq : q.natDegree ≠ 0 := fun h ↦ by
      obtain ⟨b, rfl⟩ := Polynomial.natDegree_eq_zero.mp h
      simp at h0
    have h1 := natDegree_neg (Polynomial.C a * Polynomial.derivative q)
    have h2 := Polynomial.natDegree_mul_le (p := Polynomial.C a) (q := Polynomial.derivative q)
    have h3 := Polynomial.natDegree_derivative_le q
    simp only [Polynomial.derivative_C, zero_mul, zero_sub, natDegree_C] at h1 h2 ⊢
    lia
  by_cases hq : q.natDegree = 0
  · obtain ⟨b, rfl⟩ := Polynomial.natDegree_eq_zero.mp hq
    have h2 := Polynomial.natDegree_mul_le (p := Polynomial.derivative p) (q := Polynomial.C b)
    have h3 := Polynomial.natDegree_derivative_le p
    simp only [Polynomial.derivative_C, mul_zero, sub_zero, natDegree_C] at h2 ⊢
    lia
  lia [natDegree_sub_le (Polynomial.derivative p * q) (p * Polynomial.derivative q),
    natDegree_mul_le (p := Polynomial.derivative p) (q := q),
    natDegree_mul_le (p := p) (q := Polynomial.derivative q), Polynomial.natDegree_derivative_le p,
    Polynomial.natDegree_derivative_le q]

/-- The derivative loses at least one in `intDegree`. -/
theorem IntDegreeLE.derivative {x : RatFunc K} {c : ℤ} (hx : x.IntDegreeLE c) :
    x.derivative.IntDegreeLE (c - 1) := by
  rcases hx with rfl | hx
  · rw [derivative_zero]; exact intDegreeLE_zero _
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [derivative_zero]; exact intDegreeLE_zero _
  rw [derivative_eq]
  rcases eq_or_ne (Polynomial.derivative x.num * x.denom
      - x.num * Polynomial.derivative x.denom) 0 with h0 | h0
  · rw [h0, map_zero, zero_div]; exact intDegreeLE_zero _
  refine .inr ?_
  rw [intDegree_div (algebraMap_ne_zero h0) (algebraMap_ne_zero (pow_ne_zero 2
    x.denom_ne_zero)), intDegree_polynomial, intDegree_polynomial]
  have hpow : ((x.denom ^ 2).natDegree : ℤ) = 2 * x.denom.natDegree := by
    rw [natDegree_pow]; push_cast; ring
  lia [Polynomial.natDegree_derivative_mul_sub_le h0,
    (show x.intDegree = (x.num.natDegree : ℤ) - x.denom.natDegree from rfl)]

/-- **Refined derivative bound**: the derivative of a rational function bounded at
infinity has `intDegree ≤ -2` (the constant term contributes nothing). -/
theorem IntDegreeLE.derivative_of_nonpos {x : RatFunc K} (hx : x.IntDegreeLE 0) :
    x.derivative.IntDegreeLE (-2) := by
  obtain ⟨c, hc⟩ := exists_sub_C_intDegreeLE hx
  have h : x.derivative = (x - RatFunc.C c).derivative := by
    conv_lhs => rw [show x = (x - RatFunc.C c) + RatFunc.C c from by ring]
    rw [derivative_add, derivative_C, add_zero]
  rw [h]
  exact hc.derivative.of_le (by lia)

end IntDegree

end RatFunc

end
