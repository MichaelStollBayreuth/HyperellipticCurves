/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Mathlib.RingTheory.Polynomial.ChineseRemainder
public import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Norm.Defs

import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Basic

/-!
# The norm of `R[X] ⧸ (g)` as a resultant

For monic `g`, the isomorphism `AdjoinRoot.degreeLTEquiv` of `R[X]_(deg g)` with `R[X] ⧸ (g)`
turns multiplication by `AdjoinRoot.mk g p` into `Polynomial.mulModByMonic`, the upper-left block
of the block-triangular factor `Polynomial.sylvesterBlock` of the Sylvester map of `g` and `p`.
Taking determinants gives `N(mk g p) = Res(g, p)`.

## Main statements

* `AdjoinRoot.norm_mk_eq_det_mulModByMonic`: `N(mk g p) = det (Polynomial.mulModByMonic hg p)`.
* `AdjoinRoot.norm_mk_eq_resultant`: for `g` monic, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.leadingCoeff_pow_mul_norm_mk_eq_resultant`, `AdjoinRoot.norm_mk_C`,
  `AdjoinRoot.leadingCoeff_mul_norm_of_sub_root`: the same for an invertible leading coefficient.
* `AdjoinRoot.isSquare_mul_norm_mk_of_dvd_sq_sub`: for `a ∣ b ^ 2 - f`, the norm of `a(θ)` is a
  square up to an explicit constant.

The first two statements are vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`),
the others are new; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]}

/-- The norm of `mk g p` is the determinant of multiplication by `p` on `R[X]_(g.natDegree)`,
because `AdjoinRoot.degreeLTEquiv hg` conjugates the latter into multiplication by `mk g p`. -/
theorem norm_mk_eq_det_mulModByMonic [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  rw [Algebra.norm_apply, ← det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [comp_apply, LinearEquiv.coe_coe, symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    mul_apply']
  rw [mk_modByMonic, map_mul]

/-- The norm of `AdjoinRoot.mk g p` over the base ring, for `g` monic, is the resultant of `g`
and `p`. Equivalently, it is the product of the values of `p` at the roots of `g`. -/
theorem norm_mk_eq_resultant (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p := by
  nontriviality R
  set b₁ := ((degreeLT.basis R g.natDegree).prod
    (degreeLT.basis R p.natDegree)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (g.natDegree + p.natDegree)
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← toMatrix_comp b₁ b₁ b₂, sylvesterMap_one_comp_sylvesterBlock]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    hg.resultant_one_right, one_mul]

/-- **Norms and resultants**: for `f` with invertible leading coefficient `c`, the norm of `p(θ)`
in `R[X] ⧸ (f)` is `c⁻¹ ^ deg p * Res(f, p)`. This is `AdjoinRoot.norm_mk_eq_resultant` without
the hypothesis that `f` is monic: `AdjoinRoot.algEquivOfAssociated` identifies `R[X] ⧸ (f)` with
`R[X] ⧸ (c⁻¹ * f)`, and `Polynomial.resultant_C_mul_left` compares the resultants. -/
theorem leadingCoeff_pow_mul_norm_mk_eq_resultant {f : R[X]} (hf : IsUnit f.leadingCoeff)
    (p : R[X]) : f.leadingCoeff ^ p.natDegree * Algebra.norm R (mk f p) = f.resultant p := by
  obtain ⟨u, hu⟩ := hf
  have hm : (C (↑u⁻¹ : R) * f).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by simp [← hu])
  rw [← Algebra.norm_eq_of_algEquiv (algEquivOfAssociated R _ _
      (associated_unit_mul_left f _ (isUnit_C.mpr u⁻¹.isUnit)).symm), algEquivOfAssociated_mk,
    norm_mk_eq_resultant hm, natDegree_C_mul_of_isUnit u⁻¹.isUnit, resultant_C_mul_left, ← hu,
    ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

theorem norm_mk_C {f : R[X]} (hf : IsUnit f.leadingCoeff) (r : R) :
    Algebra.norm R (mk f (C r)) = r ^ f.natDegree := by
  simpa using leadingCoeff_pow_mul_norm_mk_eq_resultant hf (C r)

/-- For `g` with invertible leading coefficient `c`, the norm of `x - θ` in `R[X] ⧸ (g)` is
`c⁻¹ * g x`: the case `p = x - X` of `AdjoinRoot.leadingCoeff_pow_mul_norm_mk_eq_resultant`. -/
theorem leadingCoeff_mul_norm_of_sub_root (hg : IsUnit g.leadingCoeff) (x : R) :
    g.leadingCoeff * Algebra.norm R (of g x - root g) = g.eval x := by
  nontriviality R
  have hd : (C x - X).natDegree = 1 := by compute_degree!
  have h := leadingCoeff_pow_mul_norm_mk_eq_resultant hg (C x - X)
  rwa [hd, pow_one, resultant_C_sub_X _ _ le_rfl, map_sub, mk_C, mk_X] at h

/-- If `f` is a square modulo `a`, then the norm of `a(θ)` in `K[X] ⧸ (f)` is a square up to the
factor `(-1) ^ (deg f * deg a) * lc(f) ^ deg a * lc(a) ^ deg f`: by
`AdjoinRoot.leadingCoeff_pow_mul_norm_mk_eq_resultant` and `Polynomial.resultant_comm`, the
product is `lc(a) ^ deg f * Res(a, f)`, a square by
`Polynomial.isSquare_leadingCoeff_pow_mul_resultant_of_dvd_sq_sub`. -/
theorem isSquare_mul_norm_mk_of_dvd_sq_sub {K : Type*} [Field K] {f a b : K[X]} (hf : f ≠ 0)
    (h : a ∣ b ^ 2 - f) :
    IsSquare ((-1) ^ (f.natDegree * a.natDegree) * f.leadingCoeff ^ a.natDegree *
      a.leadingCoeff ^ f.natDegree * Algebra.norm K (mk f a)) := by
  obtain ⟨s, hs⟩ := isSquare_leadingCoeff_pow_mul_resultant_of_dvd_sq_sub h
  have hN := leadingCoeff_pow_mul_norm_mk_eq_resultant
    (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf)) a
  rw [resultant_comm] at hN
  have hsgn : (-1 : K) ^ (f.natDegree * a.natDegree) * (-1) ^ (f.natDegree * a.natDegree) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  refine ⟨s, hs ▸ ?_⟩
  linear_combination ((-1) ^ (f.natDegree * a.natDegree) * a.leadingCoeff ^ f.natDegree) * hN +
    (a.leadingCoeff ^ f.natDegree * a.resultant f) * hsgn

end AdjoinRoot
