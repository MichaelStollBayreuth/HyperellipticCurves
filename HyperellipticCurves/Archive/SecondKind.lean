/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.Mathlib.FieldTheory.RatFunc.Degree
public import HyperellipticCurves.Curve.InftyPlace
public import HyperellipticCurves.Disks.CurvePoint
public import HyperellipticCurves.RedJ.RedIdealPrincipal
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

/-!
# Differentials of the second kind: the holomorphic-differential classification

For the odd-degree hyperelliptic curve `y² = f(x)` (`deg f = 2g + 1`), the regular
differentials are exactly `P(x)·dx/y` with `deg P ≤ g - 1` (`ChabautyColeman.RegularDiff`).
This file proves the **infinity half** of the classification of holomorphic differentials:
a coordinate-ring differential `(P + Q·y)·dx/y` that is holomorphic at the point at infinity
has vanishing `y`-part and a regular `x`-numerator.

The order at infinity of the function `P + Q·y` is `ord_∞ = -deg(P² - f·Q²)`
(`ChabautyColeman.inftyOrd_toHypField`), and `dx/y` has `ord_∞(dx/y) = 2g - 2`; so holomorphy
of the differential at infinity is `deg(P² - f·Q²) ≤ 2g - 2`
(`ChabautyColeman.eq_zero_and_degree_lt_genus_of_inftyOrd_ge`). The parity of `deg f = 2g + 1`
then forces `Q = 0` (the term `f·Q²` has odd degree `≥ 2g + 1`, which cannot be cancelled) and
`deg P ≤ g - 1` (`ChabautyColeman.eq_zero_and_degree_lt_genus_of_natDegree_norm_le`, the
arithmetic core).

The **affine half** — a differential holomorphic at every affine point is a coordinate-ring
element `P + Q·y` — is the normality of `ChabautyColeman.HypRing` (a Dedekind domain), i.e.
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`. Assembling the two halves
(`ChabautyColeman.exists_regular_numerator_of_holomorphic`) classifies holomorphic differentials
as `RegularDiff`, the regularity content of clause (c) of `thm:omega-prime-global`: a function
`φ ∈ F_K` with `φ·dx/y` holomorphic everywhere is `P(x)` with `deg P < g`.

The main theorems do not depend on this file: the trace-form route exhibits the numerator
polynomial outright instead of deducing its existence from holomorphy. The classification is
general curve theory; the `ord_∞` API it is built on lives in
`HyperellipticCurves.Curve.InftyPlace`, which the main development uses.
-/

@[expose] public section

open Polynomial IsDedekindDomain

namespace ChabautyColeman

variable {K : Type*} [Field K] {f : K[X]}

/-- **The infinity-degree classification** (differentials of the second kind, arithmetic core):
if the norm `P² - f·Q²` of a coordinate-ring function `P + Q·y` has degree `≤ 2g - 2` (i.e.
`deg(P² - f·Q²) + 3 ≤ deg f`), then the `y`-part vanishes (`Q = 0`) and the `x`-part is a
regular numerator (`deg P < g`). The parity of `deg f = 2g + 1` forbids the odd-degree term
`f·Q²`: if `Q ≠ 0` then `deg(f·Q²) ≥ 2g + 1` is odd and cannot be cancelled by the even-degree
`P²`, so `deg(P² - f·Q²) ≥ deg f`, contradicting the hypothesis. -/
theorem eq_zero_and_degree_lt_genus_of_natDegree_norm_le (hodd : Odd f.natDegree) {P Q : K[X]}
    (hle : (P ^ 2 - f * Q ^ 2).natDegree + 3 ≤ f.natDegree) :
    Q = 0 ∧ P.degree < genus f := by
  have hf : f ≠ 0 := fun h ↦ by simp [h] at hodd
  have hdP : (P ^ 2).natDegree = 2 * P.natDegree := by rw [natDegree_pow]
  have hg := two_mul_genus_add_one hodd
  have hQ : Q = 0 := by
    by_contra hQ
    have hdfQ : (f * Q ^ 2).natDegree = f.natDegree + 2 * Q.natDegree := by
      rw [natDegree_mul hf (pow_ne_zero 2 hQ), natDegree_pow]
    have hne : (P ^ 2).natDegree ≠ (f * Q ^ 2).natDegree := by
      rw [hdP, hdfQ]; rcases hodd with ⟨k, hk⟩; lia
    have hbig : f.natDegree ≤ (P ^ 2 - f * Q ^ 2).natDegree := by
      rw [sub_eq_add_neg]
      rcases lt_or_gt_of_ne hne with h | h
      · rw [natDegree_add_eq_right_of_natDegree_lt (by rwa [natDegree_neg]), natDegree_neg, hdfQ]
        lia
      · rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [natDegree_neg]), hdP]
        rw [hdfQ] at h; lia
    lia
  subst hQ
  refine ⟨rfl, ?_⟩
  have h0 : f * (0 : K[X]) ^ 2 = 0 := by ring
  rw [h0, sub_zero, hdP] at hle
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · rw [degree_eq_natDegree hP, Nat.cast_lt]; lia

variable [Fact (Odd f.natDegree)]

/-- **Holomorphy at infinity forces regularity** (differentials of the second kind): a
coordinate-ring differential `(P + Q·y)·dx/y` whose order at infinity is `≥ 0` — equivalently
`ord_∞(P + Q·y) ≥ -(2g - 2)`, since `ord_∞(dx/y) = 2g - 2` — has vanishing `y`-part and a
regular `x`-numerator (`Q = 0`, `deg P < g`, i.e. `P ∈ RegularDiff`). -/
theorem eq_zero_and_degree_lt_genus_of_inftyOrd_ge {P Q : K[X]}
    (hge : -(2 * (genus f : ℤ) - 2) ≤ inftyOrd (HypRing.toHypField f (⟨P, Q⟩ : HypRing K f))) :
    Q = 0 ∧ P.degree < genus f := by
  have hodd : Odd f.natDegree := Fact.out
  rw [inftyOrd_toHypField] at hge
  have hg := two_mul_genus_add_one hodd
  exact eq_zero_and_degree_lt_genus_of_natDegree_norm_le hodd (by lia)

section InftyComponents

open RatFunc

/-- **Assembly direction of the infinite-order component computation**: componentwise
`intDegree` bounds give a lower bound on `ChabautyColeman.inftyOrd`. -/
theorem neg_le_inftyOrd {ξ : HypField K f} {r i c : ℤ}
    (hre : ξ.re.IntDegreeLE r) (him : ξ.im.IntDegreeLE i)
    (h1 : 2 * r ≤ c) (h2 : (f.natDegree : ℤ) + 2 * i ≤ c) (h0 : 0 ≤ c) :
    -c ≤ inftyOrd ξ := by
  have hnorm : (ξ.re ^ 2 - algebraMap K[X] (RatFunc K) f * ξ.im ^ 2).IntDegreeLE c := by
    rw [sub_eq_add_neg, sq, sq]
    exact ((hre.mul hre).of_le (by lia)).add
      (((intDegreeLE_algebraMap f).mul (him.mul him)).of_le (by lia)).neg
  rw [inftyOrd, HypField.norm_eq]
  rcases hnorm with hz | hb
  · rw [hz, intDegree_zero]
    lia
  · lia

/-- **Decomposition direction**: a function bounded at the infinite place has both
components bounded — `intDegree ≤ 0` for the `x`-part and `intDegree ≤ -(g+1)` for the
`y`-part (the parities `2a` versus `2b + (2g+1)` cannot cancel). -/
theorem intDegreeLE_re_im_of_inftyOrd_nonneg {ξ : HypField K f} (hξ : 0 ≤ inftyOrd ξ) :
    ξ.re.IntDegreeLE 0 ∧ ξ.im.IntDegreeLE (-(genus f : ℤ) - 1) := by
  have hfd : f.natDegree = 2 * genus f + 1 := (two_mul_genus_add_one Fact.out).symm
  have hf0 : f ≠ 0 := fun h ↦ by rw [h] at hfd; simp at hfd
  have hF : algebraMap K[X] (RatFunc K) f ≠ 0 := algebraMap_ne_zero hf0
  rw [inftyOrd, HypField.norm_eq] at hξ
  rcases eq_or_ne ξ.im 0 with him | him
  · rw [him] at hξ ⊢
    refine ⟨?_, intDegreeLE_zero _⟩
    rcases eq_or_ne ξ.re 0 with hre | hre
    · exact .inl hre
    rw [show ξ.re ^ 2 - algebraMap K[X] (RatFunc K) f * 0 ^ 2 = ξ.re ^ 2 from by ring, sq,
      intDegree_mul hre hre] at hξ
    exact .inr (by lia)
  rcases eq_or_ne ξ.re 0 with hre | hre
  · rw [hre] at hξ ⊢
    refine ⟨intDegreeLE_zero _, .inr ?_⟩
    rw [show (0 : RatFunc K) ^ 2 - algebraMap K[X] (RatFunc K) f * ξ.im ^ 2
        = -(algebraMap K[X] (RatFunc K) f * ξ.im ^ 2) from by ring, intDegree_neg,
      intDegree_mul hF (pow_ne_zero 2 him), sq, intDegree_mul him him,
      intDegree_polynomial] at hξ
    lia
  have hsq : (ξ.re ^ 2).intDegree = 2 * ξ.re.intDegree := by
    rw [sq, intDegree_mul hre hre]
    ring
  have hfi : (algebraMap K[X] (RatFunc K) f * ξ.im ^ 2).intDegree
      = (f.natDegree : ℤ) + 2 * ξ.im.intDegree := by
    rw [intDegree_mul hF (pow_ne_zero 2 him), sq, intDegree_mul him him,
      intDegree_polynomial]
    ring
  have hne : (ξ.re ^ 2).intDegree
      ≠ (algebraMap K[X] (RatFunc K) f * ξ.im ^ 2).intDegree := by
    rw [hsq, hfi]
    lia
  rw [intDegree_sub_eq_max (pow_ne_zero 2 hre) (mul_ne_zero hF (pow_ne_zero 2 him)) hne,
    hsq, hfi] at hξ
  have hm : max (2 * ξ.re.intDegree) ((f.natDegree : ℤ) + 2 * ξ.im.intDegree) ≤ 0 := by
    lia
  have ha := (le_max_left (2 * ξ.re.intDegree)
    ((f.natDegree : ℤ) + 2 * ξ.im.intDegree)).trans hm
  have hb := (le_max_right (2 * ξ.re.intDegree)
    ((f.natDegree : ℤ) + 2 * ξ.im.intDegree)).trans hm
  exact ⟨.inr (by lia), .inr (by lia)⟩

end InftyComponents

section InftyIntegral

open RatFunc

variable {K : Type*} [Field K] {f : K[X]} [Fact (Odd f.natDegree)]

/-! ### The ring of functions integral at infinity -/

theorem inftyOrd_zero : inftyOrd (0 : HypField K f) = 0 := by
  have h := inftyOrd_toHypField (f := f) 0 0
  rw [show (⟨0, 0⟩ : HypRing K f) = 0 from rfl, map_zero] at h
  simpa using h

theorem inftyOrd_one : inftyOrd (1 : HypField K f) = 0 := by
  rw [inftyOrd, map_one, intDegree_one, neg_zero]

theorem inftyOrd_inv {g : HypField K f} (hg : g ≠ 0) : inftyOrd g⁻¹ = -inftyOrd g := by
  have h := inftyOrd_mul hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, inftyOrd_one] at h
  lia

theorem inftyOrd_nonneg_iff {ξ : HypField K f} :
    0 ≤ inftyOrd ξ ↔ ξ.re.IntDegreeLE 0 ∧ ξ.im.IntDegreeLE (-(genus f : ℤ) - 1) := by
  refine ⟨intDegreeLE_re_im_of_inftyOrd_nonneg, fun ⟨hre, him⟩ ↦ ?_⟩
  have h := neg_le_inftyOrd hre him (c := 0) (by lia) ?_ le_rfl
  · lia
  · rw [(two_mul_genus_add_one Fact.out).symm]
    push_cast
    lia

/-- **A coordinate-ring function without a pole at infinity is a constant**: `ord_∞` of
`P + Q·y` is `-deg(P² - f·Q²)`, and the odd degree of `f` forces `Q = 0` and `deg P ≤ 0`.
Equivalently: a function regular at every place is constant. -/
theorem exists_eq_C_of_inftyOrd_nonneg {z : HypRing K f}
    (h : 0 ≤ inftyOrd (HypRing.toHypField f z)) :
    ∃ c : K, z = ⟨Polynomial.C c, 0⟩ := by
  obtain ⟨hre, him⟩ := intDegreeLE_re_im_of_inftyOrd_nonneg h
  rw [HypRing.re_toHypField] at hre
  rw [HypRing.im_toHypField] at him
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have him0 : z.im = 0 := by
    rcases him with h0 | hlt
    · exact hinj (by rw [h0, map_zero])
    · rw [RatFunc.intDegree_polynomial] at hlt
      lia
  refine ⟨z.re.coeff 0, ?_⟩
  have hre0 : z.re = Polynomial.C (z.re.coeff 0) := by
    rcases hre with h0 | hlt
    · have hz : z.re = 0 := hinj (by rw [h0, map_zero])
      rw [hz]
      simp
    · rw [RatFunc.intDegree_polynomial] at hlt
      exact eq_C_of_natDegree_eq_zero (by lia)
  exact QuadraticAlgebra.ext hre0 him0

theorem inftyOrd_add_nonneg {ξ η : HypField K f} (hξ : 0 ≤ inftyOrd ξ)
    (hη : 0 ≤ inftyOrd η) : 0 ≤ inftyOrd (ξ + η) := by
  rw [inftyOrd_nonneg_iff] at hξ hη ⊢
  exact ⟨by simpa using hξ.1.add hη.1, by simpa using hξ.2.add hη.2⟩

theorem inftyOrd_neg_nonneg {ξ : HypField K f} (hξ : 0 ≤ inftyOrd ξ) :
    0 ≤ inftyOrd (-ξ) := by
  rw [inftyOrd_nonneg_iff] at hξ ⊢
  exact ⟨by simpa using hξ.1.neg, by simpa using hξ.2.neg⟩

theorem inftyOrd_mul_nonneg {ξ η : HypField K f} (hξ : 0 ≤ inftyOrd ξ)
    (hη : 0 ≤ inftyOrd η) : 0 ≤ inftyOrd (ξ * η) := by
  rcases eq_or_ne ξ 0 with rfl | hξ0
  · rw [zero_mul, inftyOrd_zero]
  rcases eq_or_ne η 0 with rfl | hη0
  · rw [mul_zero, inftyOrd_zero]
  rw [inftyOrd_mul hξ0 hη0]
  lia

/-- The subring of functions with nonnegative order at infinity. -/
noncomputable def inftyIntegers (K : Type*) [Field K] (f : K[X]) [Fact (Odd f.natDegree)] :
    Subring (HypField K f) where
  carrier := {g | 0 ≤ inftyOrd g}
  zero_mem' := by simp [Set.mem_ofPred_eq, inftyOrd_zero]
  one_mem' := by simp [Set.mem_ofPred_eq, inftyOrd_one]
  add_mem' := inftyOrd_add_nonneg
  neg_mem' := inftyOrd_neg_nonneg
  mul_mem' := inftyOrd_mul_nonneg

@[simp]
theorem mem_inftyIntegers {g : HypField K f} : g ∈ inftyIntegers K f ↔ 0 ≤ inftyOrd g :=
  Iff.rfl

/-- **Infinity-integrality of the inverse matrix**: if all entries of a square matrix over
the function field have nonnegative order at infinity and the determinant has order
exactly `0`, then the entries of the inverse matrix also have nonnegative order. -/
theorem inftyOrd_inv_matrix_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) (HypField K f)}
    (hA : ∀ i j, 0 ≤ inftyOrd (A i j)) (hd0 : A.det ≠ 0) (hdet : inftyOrd A.det = 0)
    (i j : Fin n) : 0 ≤ inftyOrd (A⁻¹ i j) := by
  have hadj : 0 ≤ inftyOrd (A.adjugate i j) := by
    set A' : Matrix (Fin n) (Fin n) (inftyIntegers K f) :=
      Matrix.of fun i j ↦ ⟨A i j, hA i j⟩ with hA'
    have hmap : A = ((inftyIntegers K f).subtype).mapMatrix A' := by
      refine Matrix.ext fun i j ↦ rfl
    rw [hmap, ← RingHom.map_adjugate, RingHom.mapMatrix_apply]
    exact (A'.adjugate i j).2
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rcases eq_or_ne (A.adjugate i j) 0 with hz | hz
  · rw [hz, mul_zero, inftyOrd_zero]
  rw [inftyOrd_mul (inv_ne_zero hd0) hz, inftyOrd_inv hd0, hdet]
  lia

/-- Variant taking the inverse relation as a hypothesis: if `A * B = 1`, the entries of
`A` are integral at infinity, and `det A` has order `0`, then the entries of `B` are
integral at infinity. -/
theorem inftyOrd_matrix_inv_nonneg_of_mul_eq_one {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) (HypField K f)} (hmul : A * B = 1)
    (hA : ∀ i j, 0 ≤ inftyOrd (A i j)) (hdet : inftyOrd A.det = 0) (i j : Fin n) :
    0 ≤ inftyOrd (B i j) := by
  have hd0 : A.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  rw [← Matrix.inv_eq_right_inv hmul]
  exact inftyOrd_inv_matrix_nonneg hA hd0 hdet i j

end InftyIntegral

variable [NeZero (2 : K)] [Fact (Squarefree f)]

/-- **The classification of holomorphic differentials** (differentials of the second kind,
regularity content of clause (c)): a function `φ ∈ F_K` such that `φ·dx/y` is holomorphic at
every point — `v(φ) ≤ 1` at every affine place `v` (holomorphy on the affine curve, since `dx/y`
has order `0` there) and `ord_∞(φ) ≥ -(2g - 2)` (holomorphy at infinity) — is a polynomial
`P(x)` with `deg P < g`, i.e. `φ·dx/y ∈ RegularDiff`. The affine condition forces `φ = P + Q·y`
a coordinate-ring element (normality of `HypRing`, `mem_integers_of_valuation_le_one`); the
infinity condition then forces `Q = 0` and `deg P < g`
(`ChabautyColeman.eq_zero_and_degree_lt_genus_of_inftyOrd_ge`). -/
theorem exists_regular_numerator_of_holomorphic (φ : HypField K f)
    (haffine : ∀ v : HeightOneSpectrum (HypRing K f), v.valuation (HypField K f) φ ≤ 1)
    (hinfty : -(2 * (genus f : ℤ) - 2) ≤ inftyOrd φ) :
    ∃ P : K[X], P.degree < genus f ∧ φ = HypRing.toHypField f ⟨P, 0⟩ := by
  obtain ⟨w, hw⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (HypField K f) φ haffine
  have hwφ : HypRing.toHypField f w = φ := hw
  have heta : (⟨w.re, w.im⟩ : HypRing K f) = w := rfl
  obtain ⟨hQ, hdeg⟩ := eq_zero_and_degree_lt_genus_of_inftyOrd_ge (P := w.re) (Q := w.im)
    (by rw [heta, hwφ]; exact hinfty)
  exact ⟨w.re, hdeg, by rw [← hwφ, ← heta, hQ]⟩

end ChabautyColeman

end
