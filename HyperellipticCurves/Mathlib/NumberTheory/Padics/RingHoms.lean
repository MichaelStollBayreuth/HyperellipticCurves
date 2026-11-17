/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms

-- Beyond the sibling: Krull's intersection theorem, for the proof of
-- `PadicInt.eq_zero_of_forall_mem_range_nsmul_pow` only, and `ZMod.ringHom_eq_of_ker_eq`, for
-- `PadicInt.instSubsingletonRingHomZMod`.
import HyperellipticCurves.Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.ZMod

/-!
# Multiples in `ℤ_[p]`-modules

## Main statements

* `PadicInt.range_nsmul_eq_top_of_not_dvd`: multiplication by an integer prime to `p` is
  surjective on a `ℤ_[p]`-module.
* `PadicInt.index_range_nsmul_self`: `p ℤ_[p]` has index `p` in `ℤ_[p]`.
* `PadicInt.eq_zero_of_forall_mem_range_nsmul_pow`: in a finitely generated `ℤ_[p]`-module, only
  `0` is divisible by every power of `p`.
* `PadicInt.isUnit_toZModPow_iff`: the reductions modulo `p ^ n`, `n ≠ 0`, reflect units.
* `PadicInt.exists_eq_pow_mul_of_toZModPow_eq`, `PadicInt.valuation_eq_of_toZModPow_eq`: an element
  congruent to `p ^ n * m` modulo `p ^ k`, for `n < k`, is `p ^ n` times an element with residue
  `m`, and has valuation `n` if `m` is prime to `p`.
* `PadicInt.isSquare_toZMod_of_coe_eq_sq_add`: if `v = α ^ 2 + y` in `ℚ_[p]` with `‖y‖ < 1`, the
  residue of `v` is a square.
* `PadicInt.instSubsingletonRingHomZMod`: `PadicInt.toZMod` is the only ring homomorphism
  `ℤ_[p] → ZMod p`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- Multiplication by an integer prime to `p` is surjective on a `ℤ_[p]`-module, as the integer
is a unit of `ℤ_[p]`. -/
theorem range_nsmul_eq_top_of_not_dvd {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] {n : ℕ}
    (hn : ¬ p ∣ n) : (nsmulAddMonoidHom (α := M) n).range = ⊤ := by
  obtain ⟨u, hu⟩ := isUnit_iff.mpr (norm_natCast_eq_one_iff.mpr
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn))
  refine eq_top_iff.mpr fun x _ ↦ ⟨((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • x, ?_⟩
  rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], ← hu, smul_smul, u.mul_inv,
    one_smul]

/-- `p ℤ_[p]` is the kernel of `PadicInt.toZMod`, so its index is `p`. -/
theorem index_range_nsmul_self : (nsmulAddMonoidHom (α := ℤ_[p]) p).range.index = p := by
  have h : (nsmulAddMonoidHom (α := ℤ_[p]) p).range =
      (toZMod (p := p) : ℤ_[p] →+* ZMod p).toAddMonoidHom.ker := by
    ext x
    simp [← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton',
      mul_comm]
  rw [h, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (ZMod.ringHom_surjective _),
    AddSubgroup.card_top, Nat.card_zmod]

/-- **Krull's intersection theorem** for `ℤ_[p]`: in a finitely generated `ℤ_[p]`-module, only
`0` is divisible by every power of `p`. -/
theorem eq_zero_of_forall_mem_range_nsmul_pow {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Finite ℤ_[p] M] {a : M}
    (ha : ∀ n : ℕ, a ∈ (nsmulAddMonoidHom (α := M) (p ^ n)).range) : a = 0 := by
  have hI := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) (IsLocalRing.maximalIdeal ℤ_[p])
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  rw [← Submodule.mem_bot ℤ_[p], ← hI]
  refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
  obtain ⟨b, rfl⟩ := ha n
  rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (by simp [maximalIdeal_eq_span_p]) n)
    Submodule.mem_top

/-- `PadicInt.toZModPow n` reflects units for `n ≠ 0`: a non-unit is divisible by `p`, so its
image is nilpotent. -/
theorem isUnit_toZModPow_iff {n : ℕ} (hn : n ≠ 0) {x : ℤ_[p]} :
    IsUnit (toZModPow n x) ↔ IsUnit x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map _⟩
  by_contra hx
  have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow hn (Nat.Prime.one_lt Fact.out)⟩
  obtain ⟨y, rfl⟩ := (norm_lt_one_iff_dvd _).mp (not_isUnit_iff.mp hx)
  refine (IsNilpotent.not_isUnit ⟨n, ?_⟩) h
  rw [← map_pow, ← RingHom.mem_ker, ker_toZModPow, mul_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- An element of `ℤ_[p]` congruent to `p ^ n * m` modulo `p ^ k`, for `n < k`, is `p ^ n` times
an element with residue `m` modulo `p`. -/
theorem exists_eq_pow_mul_of_toZModPow_eq {y : ℤ_[p]} {n k : ℕ} (hnk : n < k) {m : ℤ}
    (hy : toZModPow k y = p ^ n * m) : ∃ u : ℤ_[p], y = p ^ n * u ∧ toZMod u = m := by
  have : y - p ^ n * m ∈ RingHom.ker (toZModPow k) := by simp [hy]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (ker_toZModPow (p := p) k ▸ this)
  refine ⟨m + p ^ (k - n) * t, ?_, by simp [show k - n ≠ 0 by lia]⟩
  rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnk.le, ← ht, add_sub_cancel]

/-- An element of `ℤ_[p]` congruent to `p ^ n * m` modulo `p ^ k`, for `n < k` and `m` prime
to `p`, has valuation `n`. -/
theorem valuation_eq_of_toZModPow_eq {y : ℤ_[p]} {n k : ℕ} (hnk : n < k) {m : ℤ}
    (hy : toZModPow k y = p ^ n * m) (hm : (m : ZMod p) ≠ 0) : y.valuation = n := by
  obtain ⟨u, rfl, hu⟩ := exists_eq_pow_mul_of_toZModPow_eq hnk hy
  obtain ⟨v, rfl⟩ := (isUnit_map_iff toZMod u).mp (hu ▸ hm.isUnit)
  simp [valuation_p_pow_mul n _ v.ne_zero]

/-- If `v = α ^ 2 + y` in `ℚ_[p]` with `‖y‖ < 1`, then the residue of `v` is a square. -/
theorem isSquare_toZMod_of_coe_eq_sq_add {v : ℤ_[p]} {α y : ℚ_[p]} (hy : ‖y‖ < 1)
    (h : (v : ℚ_[p]) = α ^ 2 + y) : IsSquare (toZMod v) := by
  have hα : ‖α‖ ≤ 1 := by
    refine (pow_le_one_iff_of_nonneg (norm_nonneg α) two_ne_zero).mp ?_
    rw [← norm_pow, eq_sub_of_add_eq h.symm, sub_eq_add_neg]
    exact (Padic.nonarchimedean _ _).trans (max_le v.2 ((norm_neg y).trans_le hy.le))
  have ht : toZMod (Padic.lift y hy.le) = 0 := by
    rwa [← RingHom.mem_ker, ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits]
  have hv : v = Padic.lift α hα ^ 2 + Padic.lift y hy.le := PadicInt.ext (by push_cast; exact h)
  exact ⟨toZMod (Padic.lift α hα), by rw [hv, map_add, ht, add_zero, map_pow, sq]⟩

/-- There is only one ring homomorphism `ℤ_[p] → ZMod p`, `PadicInt.toZMod`: its kernel is a
maximal ideal, hence the maximal ideal. -/
instance instSubsingletonRingHomZMod : Subsingleton (ℤ_[p] →+* ZMod p) :=
  ⟨fun f g ↦ ZMod.ringHom_eq_of_ker_eq _ _ <| by
    rw [IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective f)), IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (ZMod.ringHom_surjective g))]⟩

@[simp]
theorem cast_toZModPow_eq_toZMod {k : ℕ} (hk : k ≠ 0) (x : ℤ_[p]) :
    (toZModPow k x).cast = toZMod x :=
  congr($(Subsingleton.elim ((ZMod.castHom (dvd_pow_self p hk) (ZMod p)).comp (toZModPow k))
    toZMod) x)

end PadicInt

end
