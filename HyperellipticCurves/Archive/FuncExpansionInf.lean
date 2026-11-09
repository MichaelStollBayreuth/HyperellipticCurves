/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.WeierstrassEven
public import HyperellipticCurves.Disks.FuncExpansion
public import HyperellipticCurves.Disks.OmegaExpansionInf

import HyperellipticCurves.Archive.ForMathlib.PowerSeries
import HyperellipticCurves.ForMathlib.AdicComplete
import HyperellipticCurves.ForMathlib.Polynomial
import HyperellipticCurves.ForMathlib.PowerSeries

/-!
# The infinity-disk function expansion and its order

Its only consumer is the chart-form `thm:spec` strand
(`HyperellipticCurves.Archive.SpecializationInf`); the main theorems do not depend on it.

On the infinity residue disk the coordinates are `x = 1/u`, `y = 1/(uᵍ z)` with `u = u(z)` the
infinity coordinate series (`ChabautyColeman.infSeries`). A function `P + Q·y` has genuine poles
there; multiplying by the monomial `uᴺ·z` (with `N` large enough to clear all poles) lands the
expansion in `O⟦z⟧`:
`funcExpansionInf P Q hf N = z·(uᴺ P(1/u)) + uᴺ⁻ᵍ Q(1/u)`, i.e.
`z·aeval u (reflect N P) + aeval u (reflect (N-g) Q)`, using `aeval u (reflect M R) = uᴹ R(1/u)`
(no invertibility needed — this is why `reflect` clears the poles cleanly).

The infinity point is ramified (its own conjugate), so — as on the Weierstrass chart — the
individual order is obtained by halving the norm-conjugate decomposition, which is legitimate
because `infSeries` is *even* (`infSeries_even`, via uniqueness of the contraction fixed point).

* `funcExpansionInf_mul_conj`: `F(P,Q)·F(P,-Q) = z²·aeval u (reflect (2N) (P²-f·Q²))` (the norm).
* `order_map_funcExpansionInf`: the individual reduced order is `1 + rootMult₀ (reflect (2N) N̄)`,
  halving the norm order via `ChabautyColeman.order_map_infSeries`.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

/-- The infinity-disk expansion of the function `P + Q·y`, cleared of poles by `uᴺ·z`. -/
noncomputable def funcExpansionInf (P Q : O[X]) {f : O[X]} (hf : f.Monic) (N : ℕ) : O⟦X⟧ :=
  PowerSeries.X * aeval (infSeries hf) (reflect N P)
    + aeval (infSeries hf) (reflect (N - genus f) Q)

/-- Norm-clearing identity in the infinity coordinate `u`: reflecting `Q²` in the short window
`2(N-g)` equals `z²` times reflecting `f·Q²` in the `2N` window. The surplus `deg f = 2g+1` slots
supply `z²·aeval u (reflect (deg f) f) = u` (`infSeries_eq`). -/
private theorem aeval_reflect_sq_eq (Q : O[X]) {f : O[X]} (hf : f.Monic) (hodd : Odd f.natDegree)
    (N : ℕ) (hQ : Q.natDegree + genus f + 1 ≤ N) :
    aeval (infSeries hf) (reflect (2 * (N - genus f)) (Q ^ 2))
      = PowerSeries.X ^ 2 * aeval (infSeries hf) (reflect (2 * N) (f * Q ^ 2)) := by
  have hdf : f.natDegree = 2 * genus f + 1 := (two_mul_genus_add_one hodd).symm
  have hQ2 : (Q ^ 2).natDegree ≤ 2 * N - f.natDegree := le_trans natDegree_pow_le (by lia)
  set u := infSeries hf
  have hlhs : aeval u (reflect (2 * (N - genus f)) (Q ^ 2))
      = u * aeval u (reflect (2 * N - f.natDegree) (Q ^ 2)) := by
    rw [show 2 * (N - genus f) = (2 * N - f.natDegree) + 1 by lia, reflect_succ hQ2, map_mul,
      aeval_X]
  have hrhs : PowerSeries.X ^ 2 * aeval u (reflect (2 * N) (f * Q ^ 2))
      = u * aeval u (reflect (2 * N - f.natDegree) (Q ^ 2)) := by
    conv_lhs => rw [show (2 : ℕ) * N = f.natDegree + (2 * N - f.natDegree) by lia]
    rw [reflect_mul f (Q ^ 2) le_rfl hQ2, map_mul, ← mul_assoc,
      show PowerSeries.X ^ 2 * aeval u (reflect f.natDegree f) = u from (infSeries_eq hf).symm]
  rw [hlhs, hrhs]

/-- The infinity-disk expansion times its conjugate is `z²·aeval u (P² - f·Q²)` reflected: the
`uᴺ·z` clearing squares to `u²ᴺ·z²`, and `(uᴺP(1/u))² - f(1/u)(uᴺ⁻ᵍQ(1/u))² = u²ᴺ(P²-f Q²)(1/u)`. -/
theorem funcExpansionInf_mul_conj (P Q : O[X]) {f : O[X]} (hf : f.Monic) (hodd : Odd f.natDegree)
    (N : ℕ) (hP : P.natDegree ≤ N) (hQ : Q.natDegree + genus f + 1 ≤ N) :
    funcExpansionInf P Q hf N * funcExpansionInf P (-Q) hf N
      = PowerSeries.X ^ 2 * aeval (infSeries hf) (reflect (2 * N) (P ^ 2 - f * Q ^ 2)) := by
  have hQle : Q.natDegree ≤ N - genus f := by lia
  set u := infSeries hf with hu
  set A := aeval u (reflect N P) with hA
  set B := aeval u (reflect (N - genus f) Q) with hB
  have hconj : funcExpansionInf P (-Q) hf N = PowerSeries.X * A - B := by
    rw [funcExpansionInf, ← hA, Polynomial.reflect_neg, map_neg, ← hB]; ring
  have hA2 : A ^ 2 = aeval u (reflect (2 * N) (P ^ 2)) := by
    rw [hA, ← map_pow, pow_two, ← reflect_mul P P hP hP, ← two_mul, ← pow_two]
  have hB2 : B ^ 2 = aeval u (reflect (2 * (N - genus f)) (Q ^ 2)) := by
    rw [hB, ← map_pow, pow_two, ← reflect_mul Q Q hQle hQle, ← two_mul, ← pow_two]
  rw [funcExpansionInf, ← hA, ← hB, hconj,
    show (PowerSeries.X * A + B) * (PowerSeries.X * A - B) = PowerSeries.X ^ 2 * A ^ 2 - B ^ 2
      from by ring, hA2, hB2, aeval_reflect_sq_eq Q hf hodd N hQ, Polynomial.reflect_sub, map_sub,
    mul_sub]

/-- `X`-adic contraction uniqueness: from `d = X²·(aeval v F - aeval u F)` and `d ∣ aeval v F -
aeval u F`, the difference `d` lies in every power `(X)ⁿ` (whence `d = 0` by Hausdorffness). -/
private theorem sub_mem_pow_span_X {v u : O⟦X⟧} {F : O[X]}
    (hsub : v - u = PowerSeries.X ^ 2 * (aeval v F - aeval u F))
    (hdvd : v - u ∣ aeval v F - aeval u F) (n : ℕ) :
    v - u ∈ (Ideal.span {(PowerSeries.X : O⟦X⟧)}) ^ n := by
  set I : Ideal (O⟦X⟧) := Ideal.span {(PowerSeries.X : O⟦X⟧)} with hI
  have hX2 : (PowerSeries.X : O⟦X⟧) ^ 2 ∈ I ^ 2 :=
    Ideal.pow_mem_pow (Ideal.mem_span_singleton.mpr dvd_rfl) 2
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · simp
    · rw [pow_one, hI, Ideal.mem_span_singleton, hsub]
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by norm_num)) _
    · obtain ⟨q, hq⟩ := hdvd
      have him : v - u ∈ I ^ 2 * I ^ (m + 1) := by
        rw [hsub, hq, ← mul_assoc]
        exact Ideal.mul_mem_right q _ (Ideal.mul_mem_mul hX2 (ih (m + 1) (by lia)))
      rw [← pow_add] at him
      exact Ideal.pow_le_pow_right (by lia) him

/-- Uniqueness of the infinity coordinate series: any `v ∈ (X)` with `v = X²·F(v)` equals
`infSeries hf` (the contraction has a unique fixed point in the `X`-adic topology). -/
theorem infSeries_unique {f : O[X]} (hf : f.Monic) {v : O⟦X⟧}
    (hveq : v = PowerSeries.X ^ 2 * aeval v f.reverse) :
    v = infSeries hf := by
  set u := infSeries hf with hu
  have hueq : u = PowerSeries.X ^ 2 * aeval u f.reverse := infSeries_eq hf
  have hsub : v - u = PowerSeries.X ^ 2 * (aeval v f.reverse - aeval u f.reverse) := by
    conv_lhs => rw [hveq, hueq]
    ring
  have hdvd : v - u ∣ aeval v f.reverse - aeval u f.reverse := by
    rw [aeval_def, aeval_def, ← eval_map, ← eval_map]; exact sub_dvd_eval_sub v u _
  exact sub_eq_zero.mp (IsHausdorff.eq_zero_of_forall_mem_pow
    (I := Ideal.span {(PowerSeries.X : O⟦X⟧)}) (v - u) (sub_mem_pow_span_X hsub hdvd))

/-- The infinity coordinate series is even: `u(-z) = u(z)` (`z ↦ -z` fixes `z²`). Proved by
uniqueness of the contraction fixed point. -/
theorem infSeries_even {f : O[X]} (hf : f.Monic) :
    rescale (-1 : O) (infSeries hf) = infSeries hf := by
  refine infSeries_unique hf ?_
  conv_lhs => rw [infSeries_eq hf]
  rw [map_mul, rescale_aeval, map_pow, rescale_X, mul_pow, ← map_pow, neg_one_sq, map_one, one_mul]

/-- The infinity expansion of the conjugate `P - Q·y` is `-rescale (-1)` of that of `P + Q·y`
(the overall sign does not affect the order). -/
theorem funcExpansionInf_neg (P Q : O[X]) {f : O[X]} (hf : f.Monic) (N : ℕ) :
    funcExpansionInf P (-Q) hf N = -rescale (-1 : O) (funcExpansionInf P Q hf N) := by
  rw [funcExpansionInf, funcExpansionInf, Polynomial.reflect_neg, map_neg, map_add, map_mul,
    rescale_aeval, rescale_aeval, infSeries_even, rescale_X,
    show (PowerSeries.C (-1 : O) : O⟦X⟧) = -1 from by rw [map_neg, map_one]]
  ring

variable [IsLocalRing O]

/-- **Order matching, infinity chart (individual).** The order of the reduced infinity-disk
expansion of `P + Q·y` is `1 + rootMult₀ (reflect (2N) N̄)` where `N̄ = (P²-f·Q²)` reduced; the
two conjugate branches contribute equally because `infSeries` is even. -/
theorem order_map_funcExpansionInf (P Q : O[X]) {f : O[X]} (hf : f.Monic) (hodd : Odd f.natDegree)
    (N : ℕ) (hP : P.natDegree ≤ N) (hQ : Q.natDegree + genus f + 1 ≤ N)
    (hN : reflect (2 * N) ((P ^ 2 - f * Q ^ 2).map (residue O)) ≠ 0) :
    ((funcExpansionInf P Q hf N).map (residue O)).order
      = 1 + (reflect (2 * N) ((P ^ 2 - f * Q ^ 2).map (residue O))).rootMultiplicity 0 := by
  set ρ := residue O
  set m₀ := (reflect (2 * N) ((P ^ 2 - f * Q ^ 2).map ρ)).rootMultiplicity 0 with hm₀
  have hsc : constantCoeff ((infSeries hf).map ρ) = 0 := by simp
  have hsym : ((funcExpansionInf P (-Q) hf N).map ρ).order
      = ((funcExpansionInf P Q hf N).map ρ).order := by
    rw [funcExpansionInf_neg, map_neg, order_neg, ← rescale_map, map_neg, map_one]
    exact order_rescale_of_isUnit isUnit_one.neg _
  have hsum : ((funcExpansionInf P Q hf N).map ρ).order
      + ((funcExpansionInf P (-Q) hf N).map ρ).order = 2 + m₀ • (2 : ℕ∞) := by
    rw [← order_mul, ← map_mul, funcExpansionInf_mul_conj P Q hf hodd N hP hQ, map_mul, map_pow,
      PowerSeries.map_X, PowerSeries.map_aeval, ← reflect_map, order_mul, order_pow, order_X,
      order_aeval_of_order_sub hsc hN, map_zero, sub_zero, order_map_infSeries hf, ← hm₀]
    rfl
  rw [hsym] at hsum
  have hrhs : (2 : ℕ∞) + m₀ • (2 : ℕ∞) = ((2 + m₀ * 2 : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]; push_cast; ring
  have hle : ((funcExpansionInf P Q hf N).map ρ).order ≤ 2 + m₀ • (2 : ℕ∞) := hsum ▸ le_self_add
  have hfin : ((funcExpansionInf P Q hf N).map ρ).order ≠ ⊤ :=
    ne_top_of_le_ne_top (hrhs ▸ ENat.natCast_ne_top _) hle
  lift ((funcExpansionInf P Q hf N).map ρ).order to ℕ using hfin with m hm
  rw [hrhs] at hsum
  norm_cast at hsum ⊢
  lia

end ChabautyColeman
