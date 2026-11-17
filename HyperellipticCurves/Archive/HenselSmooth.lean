/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Series.MvPSeries
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import HyperellipticCurves.Series.PSeries
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Multivariate Hensel's lemma (smooth-point form)

The main theorems do not depend on this file: every disk parametrization goes through the
*univariate* results of `HyperellipticCurves.Series.HenselRoot` (blueprint `thm:hensel`). A
smooth-point Hensel lemma for systems over an adically complete local ring is a genuine Mathlib
gap.

`ChabautyColeman.MvPSeries.hensel_smooth`: if a system `Φ = (F i)ᵢ` of multivariate power
series over a complete local ring `O` (in the `p`-adic kit setting) satisfies `Φ(a) ≡ 0`
with `a ∈ 𝔪ⁿ` and has an invertible Jacobian `DΦ(a)` at `a` (unit determinant), then there is
a *unique* zero `z ∈ a + 𝔪ⁿ` of `Φ`.

The proof is Newton iteration `z ↦ z - DΦ(a)⁻¹ Φ(z)` (`newtonSeq`), converging in the
`𝔪`-adic metric. The engine is a second-order multivariate Taylor bound
`Φ(z + δ) - Φ(z) - DΦ(z)·δ ∈ 𝔪^{2m}` (`eval_taylor_mem`, for `δ ∈ (𝔪ᵐ)ⁿ`), proved from a
per-monomial expansion (`monomial_taylor_mem`, via a square-zero binomial in `O/𝔪^{2m}`) and a
`pderiv` reindexing (`hasSum_linMon`). The residual `Φ(zₖ)` then lies in `𝔪^{k+1}`
(`newton_invariant`); the increments are summable, the limit is a root by
`PSeries.eq_zero_of_forall_mem_pow`, and uniqueness follows from the same contraction at the (also
invertible) Jacobian at the root.

Blueprint `thm:hensel` is realized univariately by `HyperellipticCurves.Series.HenselRoot`
(existence and uniqueness of the root; the power-series dependence on parameters is not
formalized); this multivariate form is not needed.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology
open scoped MvPowerSeries.WithPiTopology Matrix

namespace ChabautyColeman.MvPSeries

section matrixAux

variable {σ : Type*} {O : Type*} [Fintype σ] [CommRing O]

/-- Entries of a matrix-vector product with an ideal-valued vector lie in the ideal. -/
theorem mulVec_mem (A : Matrix σ σ O) {v : σ → O} {I : Ideal O} (hv : ∀ j, v j ∈ I) (i : σ) :
    (A *ᵥ v) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Submodule.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (hv j)

end matrixAux

section algebra

variable {σ : Type*} {O : Type*} [CommRing O] [IsLocalRing O]

/-- The monomial values at two families congruent mod `𝔪 ^ m` differ by an element of `𝔪 ^ m`. -/
theorem prod_sub_prod_mem_pow (m : ℕ) {z w : σ → O}
    (h : ∀ i, z i - w i ∈ maximalIdeal O ^ m) (d : σ →₀ ℕ) :
    (d.prod fun s e ↦ z s ^ e) - (d.prod fun s e ↦ w s ^ e) ∈ maximalIdeal O ^ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, Finsupp.prod, Finsupp.prod,
    map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  rw [map_pow, map_pow, (Ideal.Quotient.eq).mpr (h s)]

/-- Square-zero binomial: `(x + y) ^ k = x ^ k + k * x ^ (k - 1) * y` when `y * y = 0`. -/
theorem add_pow_sq_zero {R : Type*} [CommRing R] (x y : R) (hy : y * y = 0) :
    ∀ k : ℕ, (x + y) ^ k = x ^ k + (k : R) * x ^ (k - 1) * y
  | 0 => by simp
  | (k + 1) => by
    rw [pow_succ, add_pow_sq_zero x y hy k, Nat.add_sub_cancel]
    have hxx : (k : R) * x ^ (k - 1) * x = (k : R) * x ^ k := by
      rw [mul_assoc]; cases k with
      | zero => simp
      | succ n => rw [Nat.add_sub_cancel, ← pow_succ]
    push_cast
    linear_combination ((k : R) * x ^ (k - 1)) * hy + y * hxx

/-- First-order product expansion when all pairwise `b`-products vanish. -/
theorem prod_add_lin {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] (a b : ι → R)
    (s : Finset ι) (hb : ∀ i j, b i * b j = 0) :
    ∏ i ∈ s, (a i + b i) = ∏ i ∈ s, a i + ∑ i ∈ s, b i * ∏ j ∈ s.erase i, a j := by
  induction s using Finset.induction with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, ih, Finset.prod_insert hk, Finset.sum_insert hk,
      Finset.erase_insert hk]
    have hsum : ∑ i ∈ s, b i * ∏ j ∈ (insert k s).erase i, a j
              = ∑ i ∈ s, b i * (a k * ∏ j ∈ s.erase i, a j) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Finset.erase_insert_of_ne (by rintro rfl; exact hk hi),
          Finset.prod_insert (fun h ↦ hk (Finset.mem_of_mem_erase h))]
    have hbk : b k * ∑ i ∈ s, b i * ∏ j ∈ s.erase i, a j = 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun i _ ↦ by
        rw [← mul_assoc, hb k i, zero_mul]
    have key : ∑ i ∈ s, b i * (a k * ∏ j ∈ s.erase i, a j)
             = a k * ∑ i ∈ s, b i * ∏ j ∈ s.erase i, a j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsum, key, add_mul, mul_add, mul_add, hbk, add_zero]
    ring

/-- The erase-product form of a monomial's `s`-th partial equals the `d - eₛ` form. -/
theorem prod_erase_eq {R : Type*} [CommRing R] {σ' : Type*} [DecidableEq σ']
    (w : σ' → R) (s : σ') (d : σ' →₀ ℕ) :
    w s ^ (d s - 1) * ∏ t ∈ d.support.erase s, w t ^ d t
      = (d - Finsupp.single s 1).prod (fun t e ↦ w t ^ e) := by
  classical
  rw [Finsupp.prod_of_support_subset (d - Finsupp.single s 1) Finsupp.support_tsub
    (fun t e ↦ w t ^ e) (fun i _ ↦ pow_zero (w i))]
  have hexp : ∀ t ∈ d.support.erase s,
      w t ^ ((d - Finsupp.single s 1 : σ' →₀ ℕ) t) = w t ^ d t := fun t ht ↦ by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase ht), Nat.sub_zero]
  by_cases hs : s ∈ d.support
  · rw [← Finset.mul_prod_erase _ _ hs, Finsupp.tsub_apply, Finsupp.single_eq_same,
      Finset.prod_congr rfl hexp]
  · rw [Finset.erase_eq_of_notMem hs, Finsupp.notMem_support_iff.mp hs, Nat.zero_sub, pow_zero,
      one_mul]
    exact Finset.prod_congr rfl fun t ht ↦ by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (by rintro rfl; exact hs ht), Nat.sub_zero]

/-- Per-monomial second-order Taylor bound. -/
theorem monomial_taylor_mem [DecidableEq σ] (m : ℕ) {z δ : σ → O}
    (hδ : ∀ s, δ s ∈ maximalIdeal O ^ m) (d : σ →₀ ℕ) :
    (d.prod fun t e ↦ (z t + δ t) ^ e) - (d.prod fun t e ↦ z t ^ e)
      - ∑ s ∈ d.support, (d s : O) * z s ^ (d s - 1) * δ s
          * ∏ t ∈ d.support.erase s, z t ^ d t
      ∈ maximalIdeal O ^ (2 * m) := by
  classical
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, map_sum]
  set π := Ideal.Quotient.mk (maximalIdeal O ^ (2 * m)) with hπ
  have hδ0 : ∀ s t, π (δ s) * π (δ t) = 0 := fun s t ↦ by
    rw [hπ, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, two_mul, pow_add]
    exact Ideal.mul_mem_mul (hδ s) (hδ t)
  rw [Finsupp.prod, Finsupp.prod, map_prod, map_prod]
  have hfac : ∀ t ∈ d.support, π ((z t + δ t) ^ d t)
      = π (z t) ^ d t
        + (fun t ↦ (d t : O ⧸ maximalIdeal O ^ (2 * m)) * π (z t) ^ (d t - 1) * π (δ t)) t := by
    intro t _
    rw [map_pow, map_add, add_pow_sq_zero _ _ (hδ0 t t)]
  rw [Finset.prod_congr rfl hfac,
    prod_add_lin (fun t ↦ π (z t) ^ d t)
      (fun t ↦ (d t : O ⧸ maximalIdeal O ^ (2 * m)) * π (z t) ^ (d t - 1) * π (δ t)) _
      (fun i j ↦ by
        rw [show ((d i : O ⧸ maximalIdeal O ^ (2 * m)) * π (z i) ^ (d i - 1) * π (δ i))
            * ((d j : O ⧸ _) * π (z j) ^ (d j - 1) * π (δ j))
            = ((d i : O ⧸ _) * π (z i) ^ (d i - 1)) * ((d j : O ⧸ _) * π (z j) ^ (d j - 1))
              * (π (δ i) * π (δ j)) by ring, hδ0 i j, mul_zero])]
  simp only [map_pow]
  rw [add_sub_cancel_left, sub_eq_zero]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [map_mul, map_pow, map_natCast, map_prod]

end algebra

section eval

variable {σ : Type*} {O : Type*} [CommRing O] [UniformSpace O]
  [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O]

/-- The value at a point of `𝔪 ^ m` is congruent to the constant coefficient modulo `𝔪 ^ m`. -/
theorem eval_sub_constantCoeff_mem_pow {z₀ : σ → O} (hz₀ : MvPowerSeries.HasEval z₀) (m : ℕ)
    (hmem : ∀ i, z₀ i ∈ maximalIdeal O ^ m) (h : MvPowerSeries σ O) :
    eval z₀ h - constantCoeff h ∈ maximalIdeal O ^ m := by
  classical
  have htot := hasSum_eval hz₀ h
  have hupd := htot.update 0 0
  have hval : ∀ d : σ →₀ ℕ, Function.update
      (fun d : σ →₀ ℕ ↦ coeff d h * d.prod fun s e ↦ z₀ s ^ e) 0 0 d
        ∈ maximalIdeal O ^ m := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [Function.update_of_ne hd]
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hi]
      refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ?_)
      exact Ideal.pow_mem_of_mem _ (hmem i) _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
  have hmemsum : (∑' d, Function.update
      (fun d : σ →₀ ℕ ↦ coeff d h * d.prod fun s e ↦ z₀ s ^ e) 0 0 d)
        ∈ maximalIdeal O ^ m :=
    tsum_mem ((Fact.out : IsAdic (maximalIdeal O)).isClosed_pow m) hval
  rw [hupd.tsum_eq] at hmemsum
  simpa [Finsupp.prod_zero_index, zero_sub, neg_add_eq_sub] using hmemsum

/-- First-order continuity of evaluation. -/
theorem eval_sub_eval_mem_pow {z w : σ → O} (hz : MvPowerSeries.HasEval z)
    (hw : MvPowerSeries.HasEval w) (m : ℕ) (h : ∀ i, z i - w i ∈ maximalIdeal O ^ m)
    (g : MvPowerSeries σ O) : eval z g - eval w g ∈ maximalIdeal O ^ m := by
  have hmem : ∀ d : σ →₀ ℕ, coeff d g * (d.prod fun s e ↦ z s ^ e)
      - coeff d g * (d.prod fun s e ↦ w s ^ e) ∈ maximalIdeal O ^ m := fun d ↦ by
    rw [← mul_sub]; exact Ideal.mul_mem_left _ _ (prod_sub_prod_mem_pow m h d)
  have := tsum_mem ((Fact.out : IsAdic (maximalIdeal O)).isClosed_pow m) hmem
  rwa [((hasSum_eval hz g).sub (hasSum_eval hw g)).tsum_eq] at this

/-- Reindex: the `s`-th slice of the monomial expansion sums to `eval z (∂ₛ g)`. -/
theorem hasSum_linMon [DecidableEq σ] {z : σ → O} (hz : MvPowerSeries.HasEval z) (s : σ)
    (g : MvPowerSeries σ O) :
    HasSum (fun d ↦ coeff d g * ((d s : O) * z s ^ (d s - 1)
      * ∏ t ∈ d.support.erase s, z t ^ d t)) (eval z (pderiv s g)) := by
  have hbridge : (fun d ↦ coeff d g * ((d s : O) * z s ^ (d s - 1)
      * ∏ t ∈ d.support.erase s, z t ^ d t))
    = fun d ↦ coeff d g * ((d s : O) * (d - Finsupp.single s 1).prod (fun t e ↦ z t ^ e)) := by
    funext d; rw [mul_assoc ((d s : O)), prod_erase_eq]
  rw [hbridge]
  have hinj : Function.Injective (fun e : σ →₀ ℕ ↦ e + Finsupp.single s 1) :=
    add_left_injective _
  refine (Function.Injective.hasSum_iff hinj (fun d hd ↦ ?_)).mp ?_
  · have hds : d s = 0 := by
      by_contra h
      refine hd ⟨d - Finsupp.single s 1, ?_⟩
      change d - Finsupp.single s 1 + Finsupp.single s 1 = d
      rw [tsub_add_cancel_of_le (by rwa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero])]
    simp [hds]
  · have hcomp : ((fun d ↦ coeff d g * ((d s : O)
          * (d - Finsupp.single s 1).prod (fun t e ↦ z t ^ e)))
        ∘ fun e ↦ e + Finsupp.single s 1)
        = fun e ↦ coeff e (pderiv s g) * e.prod fun t e' ↦ z t ^ e' := by
      funext e
      rw [Function.comp_apply, Finsupp.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right,
        coeff_pderiv]
      push_cast; ring
    rw [hcomp]; exact hasSum_eval hz (pderiv s g)

/-- Second-order multivariate Taylor bound for evaluation. -/
theorem eval_taylor_mem [Fintype σ] (m : ℕ) {z δ : σ → O} (hz : ∀ i, z i ∈ maximalIdeal O)
    (hzδ : ∀ i, z i + δ i ∈ maximalIdeal O) (hδ : ∀ s, δ s ∈ maximalIdeal O ^ m)
    (g : MvPowerSeries σ O) :
    eval (fun i ↦ z i + δ i) g - eval z g - ∑ s, δ s * eval z (pderiv s g)
      ∈ maximalIdeal O ^ (2 * m) := by
  classical
  have hzE := hasEval_of_mem hz
  have hzδE := hasEval_of_mem hzδ
  have hlin : HasSum (fun d ↦ coeff d g * ∑ s, ((d s : O) * z s ^ (d s - 1) * δ s
      * ∏ t ∈ d.support.erase s, z t ^ d t)) (∑ s, δ s * eval z (pderiv s g)) := by
    refine (hasSum_sum (fun s _ ↦ (hasSum_linMon hzE s g).mul_left (δ s))).congr_fun fun d ↦ ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ ↦ by ring
  have hsuppeq : ∀ d : σ →₀ ℕ, ∑ s, ((d s : O) * z s ^ (d s - 1) * δ s
        * ∏ t ∈ d.support.erase s, z t ^ d t)
      = ∑ s ∈ d.support, (d s : O) * z s ^ (d s - 1) * δ s
        * ∏ t ∈ d.support.erase s, z t ^ d t := fun d ↦
    (Finset.sum_subset (Finset.subset_univ _) fun s _ hs ↦ by
      rw [Finsupp.notMem_support_iff.mp hs]; simp).symm
  have hcomb := ((hasSum_eval hzδE g).sub (hasSum_eval hzE g)).sub hlin
  have hmem : ∀ d : σ →₀ ℕ, (coeff d g * (d.prod fun s e ↦ (z s + δ s) ^ e)
      - coeff d g * (d.prod fun s e ↦ z s ^ e))
      - coeff d g * ∑ s, ((d s : O) * z s ^ (d s - 1) * δ s
        * ∏ t ∈ d.support.erase s, z t ^ d t) ∈ maximalIdeal O ^ (2 * m) := fun d ↦ by
    rw [hsuppeq, show (coeff d g * (d.prod fun s e ↦ (z s + δ s) ^ e)
        - coeff d g * (d.prod fun s e ↦ z s ^ e))
        - coeff d g * ∑ s ∈ d.support, (d s : O) * z s ^ (d s - 1) * δ s
          * ∏ t ∈ d.support.erase s, z t ^ d t
        = coeff d g * ((d.prod fun s e ↦ (z s + δ s) ^ e) - (d.prod fun s e ↦ z s ^ e)
          - ∑ s ∈ d.support, (d s : O) * z s ^ (d s - 1) * δ s
            * ∏ t ∈ d.support.erase s, z t ^ d t) by ring]
    exact Ideal.mul_mem_left _ _ (monomial_taylor_mem m hδ d)
  have := tsum_mem ((Fact.out : IsAdic (maximalIdeal O)).isClosed_pow (2 * m)) hmem
  rwa [hcomb.tsum_eq] at this

end eval

section newton

variable {σ : Type*} {O : Type*} [CommRing O] [UniformSpace O]
  [IsLocalRing O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [Fintype σ] [DecidableEq σ]

/-- The Newton iteration `w ↦ w - J⁻¹ Φ(w)` (with `M = J⁻¹`), starting at `a`. -/
noncomputable def newtonSeq (F : σ → MvPowerSeries σ O) (M : Matrix σ σ O) (a : σ → O) :
    ℕ → σ → O
  | 0 => a
  | (k + 1) => fun i ↦ newtonSeq F M a k i - (M *ᵥ fun j ↦ eval (newtonSeq F M a k) (F j)) i

/-- The Newton iterates stay in `𝔪` and the residual `Φ(wₖ)` lies in `𝔪 ^ (k+1)`. -/
theorem newton_invariant (F : σ → MvPowerSeries σ O) (a : σ → O) (M J : Matrix σ σ O)
    (hJdef : ∀ i j, J i j = eval a (pderiv j (F i))) (hJM : J * M = 1)
    (ha : ∀ i, a i ∈ maximalIdeal O) (hF0 : ∀ i, eval a (F i) ∈ maximalIdeal O) (k : ℕ) :
    (∀ i, newtonSeq F M a k i ∈ maximalIdeal O)
      ∧ (∀ i, eval (newtonSeq F M a k) (F i) ∈ maximalIdeal O ^ (k + 1)) := by
  induction k with
  | zero => exact ⟨ha, fun i ↦ by
      change eval a (F i) ∈ maximalIdeal O ^ 1; rw [pow_one]; exact hF0 i⟩
  | succ k ih =>
    obtain ⟨hwmem, hwF⟩ := ih
    set w := newtonSeq F M a k with hw
    set incr := fun i ↦ -(M *ᵥ fun j ↦ eval w (F j)) i with hincrdef
    have hincr : ∀ i, incr i ∈ maximalIdeal O ^ (k + 1) := fun i ↦
      neg_mem (mulVec_mem M hwF i)
    have hstep : ∀ i, newtonSeq F M a (k + 1) i = w i + incr i := fun i ↦ by
      rw [hincrdef]; simp [newtonSeq, hw, sub_eq_add_neg]
    have hmem1 : ∀ i, w i - a i ∈ maximalIdeal O := fun i ↦
      sub_mem (hwmem i) (ha i)
    have hAk1 : ∀ i, w i + incr i ∈ maximalIdeal O := fun i ↦
      add_mem (hwmem i) (Ideal.pow_le_self (Nat.succ_ne_zero k) (hincr i))
    have hstepf : newtonSeq F M a (k + 1) = fun i ↦ w i + incr i := funext hstep
    have hincreq : incr = -(M *ᵥ fun j ↦ eval w (F j)) := funext fun i ↦ by rw [hincrdef]; rfl
    refine ⟨fun i ↦ hstepf ▸ hAk1 i, fun i ↦ ?_⟩
    rw [hstepf]
    have htay := eval_taylor_mem (k + 1) hwmem hAk1 hincr (F i)
    -- the linear term cancels eval w (F i) modulo 𝔪 ^ (k+2)
    have hJincr : (J *ᵥ incr) i = - eval w (F i) := by
      rw [hincreq, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hJM, Matrix.one_mulVec]
      simp
    have hJa : ∑ j, incr j * eval a (pderiv j (F i)) = - eval w (F i) := by
      rw [← hJincr]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hJdef]; ring
    have hdiff : ∑ j, incr j * eval w (pderiv j (F i))
        - ∑ j, incr j * eval a (pderiv j (F i)) ∈ maximalIdeal O ^ (k + 2) := by
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      rw [← mul_sub]
      have hmul := Ideal.mul_mem_mul (hincr j) (eval_sub_eval_mem_pow (hasEval_of_mem hwmem)
        (hasEval_of_mem ha) 1 (by simpa only [pow_one] using hmem1) (pderiv j (F i)))
      rwa [← pow_add] at hmul
    have hcancel : eval w (F i) + ∑ j, incr j * eval w (pderiv j (F i))
        ∈ maximalIdeal O ^ (k + 2) := by
      have heq : eval w (F i) + ∑ j, incr j * eval w (pderiv j (F i))
          = ∑ j, incr j * eval w (pderiv j (F i)) - ∑ j, incr j * eval a (pderiv j (F i)) := by
        rw [hJa]; ring
      rw [heq]; exact hdiff
    rw [show eval (fun i ↦ w i + incr i) (F i)
        = (eval (fun i ↦ w i + incr i) (F i) - eval w (F i)
            - ∑ j, incr j * eval w (pderiv j (F i)))
          + (eval w (F i) + ∑ j, incr j * eval w (pderiv j (F i))) by ring]
    exact add_mem (Ideal.pow_le_pow_right (by lia) htay) hcancel

/-- Existence half of `hensel_smooth`: the Newton iteration converges to a root in `a + 𝔪ⁿ`. -/
theorem newton_exists (F : σ → MvPowerSeries σ O) (a : σ → O)
    (ha : ∀ i, a i ∈ maximalIdeal O) (hF0 : ∀ i, eval a (F i) ∈ maximalIdeal O)
    (hJ : IsUnit (Matrix.of fun i j ↦ eval a (pderiv j (F i))).det) :
    ∃ z : σ → O, (∀ i, z i - a i ∈ maximalIdeal O) ∧ ∀ i, eval z (F i) = 0 := by
  classical
  set J := Matrix.of fun i j ↦ eval a (pderiv j (F i)) with hJdef0
  have hJdef : ∀ i j, J i j = eval a (pderiv j (F i)) := fun i j ↦ rfl
  have hJM : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have hinv := newton_invariant F a J⁻¹ J hJdef hJM ha hF0
  set w := newtonSeq F J⁻¹ a with hwdef
  have hg : ∀ k i, w (k + 1) i - w k i ∈ maximalIdeal O ^ (k + 1) := fun k i ↦ by
    have hstep : w (k + 1) i = w k i - (J⁻¹ *ᵥ fun j ↦ eval (w k) (F j)) i := rfl
    have hval : w (k + 1) i - w k i = -(J⁻¹ *ᵥ fun j ↦ eval (w k) (F j)) i := by
      rw [hstep]; ring
    rw [hval]; exact neg_mem (mulVec_mem _ (hinv k).2 i)
  obtain ⟨z, hza0, hzw⟩ := PSeries.exists_limit_of_sub_mem_pow w hg
  have hza : ∀ i, z i - a i ∈ maximalIdeal O := hza0
  have hzmem : ∀ i, z i ∈ maximalIdeal O := fun i ↦ by
    have := add_mem (hza i) (ha i); simpa using this
  refine ⟨z, hza, fun i ↦ PSeries.eq_zero_of_forall_mem_pow _ fun n ↦ ?_⟩
  have h1 := eval_sub_eval_mem_pow (hasEval_of_mem hzmem) (hasEval_of_mem (hinv n).1) n
    (hzw n) (F i)
  have h2 : eval (w n) (F i) ∈ maximalIdeal O ^ n :=
    Ideal.pow_le_pow_right (by lia : n ≤ n + 1) ((hinv n).2 i)
  have := add_mem h1 h2; simpa using this

/-- Uniqueness half of `hensel_smooth`: two roots in `a + 𝔪ⁿ` coincide (the Jacobian at the
root is again invertible, giving a contraction). -/
theorem newton_unique (F : σ → MvPowerSeries σ O) (a : σ → O) (ha : ∀ i, a i ∈ maximalIdeal O)
    (hJ : IsUnit (Matrix.of fun i j ↦ eval a (pderiv j (F i))).det) {y z : σ → O}
    (hya : ∀ i, y i - a i ∈ maximalIdeal O) (hyroot : ∀ i, eval y (F i) = 0)
    (hza : ∀ i, z i - a i ∈ maximalIdeal O) (hzroot : ∀ i, eval z (F i) = 0) : y = z := by
  classical
  set J := Matrix.of fun i j ↦ eval a (pderiv j (F i)) with hJdef0
  have hymem : ∀ i, y i ∈ maximalIdeal O := fun i ↦ by
    have := add_mem (hya i) (ha i); simpa using this
  have hzmem : ∀ i, z i ∈ maximalIdeal O := fun i ↦ by
    have := add_mem (hza i) (ha i); simpa using this
  have hyz1 : ∀ i, y i - z i ∈ maximalIdeal O := fun i ↦ by
    have := sub_mem (hya i) (hza i); simpa using this
  set J' := Matrix.of fun i j ↦ eval z (pderiv j (F i)) with hJ'def
  have hJ'a : ∀ i j, J' i j - J i j ∈ maximalIdeal O := fun i j ↦ by
    rw [hJ'def, hJdef0, Matrix.of_apply, Matrix.of_apply, ← pow_one (maximalIdeal O)]
    exact eval_sub_eval_mem_pow (hasEval_of_mem hzmem) (hasEval_of_mem ha) 1
      (fun i ↦ by rw [pow_one]; exact hza i) (pderiv j (F i))
  have hdet : (Ideal.Quotient.mk (maximalIdeal O)) J'.det
      = (Ideal.Quotient.mk (maximalIdeal O)) J.det := by
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply]
    exact (Ideal.Quotient.eq).mpr (hJ'a i j)
  have hJ'unit : IsUnit J'.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← Ideal.Quotient.eq_zero_iff_mem, hdet,
      Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.notMem_maximalIdeal]
    exact hJ
  have hJ'inv : J'⁻¹ * J' = 1 := Matrix.nonsing_inv_mul J' hJ'unit
  have huniq : ∀ n i, y i - z i ∈ maximalIdeal O ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro i; rw [pow_one]; exact hyz1 i
    | succ n ihn =>
      have hJ'v : ∀ i, (J' *ᵥ fun j ↦ y j - z j) i ∈ maximalIdeal O ^ (n + 2) := fun i ↦ by
        have htay := eval_taylor_mem (n + 1) hzmem
          (fun j ↦ by rw [show z j + (y j - z j) = y j by ring]; exact hymem j) ihn (F i)
        rw [show (fun i ↦ z i + (y i - z i)) = y from funext fun i ↦ by ring,
          hyroot i, hzroot i] at htay
        have hsum : (J' *ᵥ fun j ↦ y j - z j) i
            = ∑ s, (y s - z s) * eval z (pderiv s (F i)) := by
          simp only [Matrix.mulVec, dotProduct, hJ'def, Matrix.of_apply]
          exact Finset.sum_congr rfl fun s _ ↦ mul_comm _ _
        rw [hsum]
        exact Ideal.pow_le_pow_right (by lia : n + 2 ≤ 2 * (n + 1)) (by simpa using neg_mem htay)
      intro i
      have hinvid : (fun j ↦ y j - z j) i = (J'⁻¹ *ᵥ (J' *ᵥ fun j ↦ y j - z j)) i := by
        rw [Matrix.mulVec_mulVec, hJ'inv, Matrix.one_mulVec]
      rw [show y i - z i = (fun j ↦ y j - z j) i from rfl, hinvid]
      exact mulVec_mem _ hJ'v i
  exact funext fun i ↦ sub_eq_zero.mp (PSeries.eq_zero_of_forall_mem_pow (y i - z i) fun n ↦ by
    cases n with
    | zero => simp
    | succ n => exact huniq n i)

/-- **Multivariate Hensel's lemma (smooth-point form).** A system of power series `F` over the
complete local ring `O` with `Φ(a) ≡ 0` (`a ∈ 𝔪ⁿ`) and invertible Jacobian at `a` has a unique
zero in `a + 𝔪ⁿ`. -/
theorem hensel_smooth (F : σ → MvPowerSeries σ O) (a : σ → O)
    (ha : ∀ i, a i ∈ maximalIdeal O) (hF0 : ∀ i, eval a (F i) ∈ maximalIdeal O)
    (hJ : IsUnit (Matrix.of fun i j ↦ eval a (pderiv j (F i))).det) :
    ∃! z : σ → O, (∀ i, z i - a i ∈ maximalIdeal O) ∧ ∀ i, eval z (F i) = 0 := by
  obtain ⟨z, hza, hzroot⟩ := newton_exists F a ha hF0 hJ
  exact ⟨z, ⟨hza, hzroot⟩, fun y ⟨hya, hyroot⟩ ↦ newton_unique F a ha hJ hya hyroot hza hzroot⟩

end newton

end ChabautyColeman.MvPSeries

end
