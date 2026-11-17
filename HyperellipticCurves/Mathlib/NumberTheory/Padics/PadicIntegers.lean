/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.NumberTheory.Padics.PadicIntegers`: `IsAdic`, for the statements.
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# The topology of `ℤ_[p]` is the adic topology of its maximal ideal

The ideals `p ^ n * ℤ_[p]` are exactly the closed balls of radius `p ^ (-n)`, which are open and
form a neighborhood basis of `0`. The statement is registered as a `Fact` instance, so that
`ℤ_[p]` satisfies the standing hypotheses of the `p`-adic kit
(`HyperellipticCurves.Series.PSeries`).

## Main statements

* `PadicInt.isAdic`: the metric topology of `ℤ_[p]` is the adic topology of its maximal ideal.
* `PadicInt.instFactIsAdic`: the same, as a `Fact` instance.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

open IsLocalRing

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The metric topology of `ℤ_p` is the adic topology of its maximal ideal. -/
theorem isAdic : IsAdic (maximalIdeal ℤ_[p]) := by
  rw [isAdic_iff]
  constructor
  · intro n
    refine Metric.isOpen_iff.mpr fun x hx ↦
      ⟨(p : ℝ) ^ (-n : ℤ), zpow_pos (mod_cast hp.out.pos) _, fun y hy ↦ ?_⟩
    rw [SetLike.mem_coe, maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      ← norm_le_pow_iff_mem_span_pow] at hx ⊢
    rw [Metric.mem_ball, dist_eq_norm] at hy
    calc ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by simpa using nonarchimedean (y - x) x
      _ ≤ (p : ℝ) ^ (-n : ℤ) := max_le hy.le hx
  · intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
    refine ⟨k, fun x hx ↦ hball ?_⟩
    rw [SetLike.mem_coe, maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      ← norm_le_pow_iff_mem_span_pow] at hx
    rw [Metric.mem_ball, dist_zero_right]
    exact hx.trans_lt hk

/-- Registered as a `Fact` so that `ℤ_[p]` meets the standing hypotheses of the `p`-adic kit. -/
instance instFactIsAdic : Fact (IsAdic (maximalIdeal ℤ_[p])) := ⟨isAdic⟩

end PadicInt

end
