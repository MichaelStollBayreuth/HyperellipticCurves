/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

-- Beyond the sibling, for the proofs only: `Ideal.smul_top_eq_self` and
-- `Module.Basis.mem_smul_top_iff` (the mirror of `Mathlib.RingTheory.Ideal.Operations`),
-- `Ideal.Quotient.mk_span_one_sub` (the mirror of `Mathlib.RingTheory.Ideal.Quotient.Basic`),
-- `IsIdempotentElem.mul_mem_pow_of_mk_mem_map_pow` (the mirror of
-- `Mathlib.RingTheory.Ideal.Quotient.Operations`), and the tactic `linear_combination`.
import HyperellipticCurves.Mathlib.RingTheory.Ideal.Operations
import HyperellipticCurves.Mathlib.RingTheory.Ideal.Quotient.Basic
import HyperellipticCurves.Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic consequences of adic completeness

Algebraic (as opposed to topological) results for `I`-adically complete rings and modules:
convergence of sequences with differences in growing powers of `I`, the `I`-adic order of a
nonzero element, the dependence on the ideal only up to cofinality of the filtrations, the
passage to the quotient by an idempotent, the lifting of idempotents, and modules with a finite
basis.

## Main statements

* `IsPrecomplete.exists_limit`: nonarchimedean telescoping — a sequence whose consecutive
  differences lie in `I ^ (k + 1)` has a limit, approximated to order `n` by its `n`-th term.
* `IsHausdorff.eq_zero_of_forall_mem_pow`, `IsHausdorff.exists_mem_pow_and_notMem_pow_succ`:
  Hausdorffness, and the `I`-adic order it gives a nonzero element.
* `isAdicComplete_of_le_of_pow_le`, `isAdicComplete_of_pow`: adic completeness depends on the
  ideal only through the cofinality class of its filtration.
* `IsIdempotentElem.isAdicComplete_quotient`: adic completeness passes to the quotient
  `A ⧸ (1 - ε)` by an idempotent, for the image of the ideal.
* `IsAdicComplete.exists_isIdempotentElem_of_sq_sub_mem`: idempotents lift along an adically
  complete ideal, by the Newton iteration `x ↦ 3 * x ^ 2 - 2 * x ^ 3`.
* `Module.Basis.isAdicComplete`: a module with a finite basis over an adically complete ring is
  adically complete.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

variable {R : Type*} [CommRing R] {I : Ideal R}

/-! ### Convergence in an adically complete ring -/

/-- Nonarchimedean telescoping in an `I`-adically precomplete ring: if consecutive iterates
`wₖ` differ by an element of `I^(k+1)`, the sequence converges to a limit `z` with `z - wₙ ∈ Iⁿ`
for every `n`. Generalizes `PSeries.exists_limit_of_sub_mem_pow` (maximal-ideal case). -/
theorem IsPrecomplete.exists_limit [IsPrecomplete I R] (w : ℕ → R)
    (hstep : ∀ k, w (k + 1) - w k ∈ I ^ (k + 1)) :
    ∃ z : R, z - w 0 ∈ I ∧ ∀ n, z - w n ∈ I ^ n := by
  have hle : ∀ m n, m ≤ n → w n - w m ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : w (n + 1) - w n ∈ I ^ m := Ideal.pow_le_pow_right (by lia) (hstep n)
      have : w (n + 1) - w m = (w (n + 1) - w n) + (w n - w m) := by ring
      rw [this]; exact add_mem h1 ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹_› (f := w) fun {m n} hmn ↦ by
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self]
    exact (Ideal.neg_mem_iff _).mp (by simpa using hle m n hmn)
  have hLn : ∀ n, L - w n ∈ I ^ n := fun n ↦ by
    have := hL n
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at this
    exact (Ideal.neg_mem_iff _).mp (by simpa using this)
  refine ⟨L, ?_, hLn⟩
  have h1 : w 1 - w 0 ∈ I := by simpa using hstep 0
  have : L - w 0 = (L - w 1) + (w 1 - w 0) := by ring
  rw [this]; exact add_mem (by simpa using hLn 1) h1

/-- Hausdorffness: an element in every power of `I` is zero. Generalizes
`PSeries.eq_zero_of_forall_mem_pow` (maximal-ideal case). -/
theorem IsHausdorff.eq_zero_of_forall_mem_pow [IsHausdorff I R] (x : R) (hx : ∀ n, x ∈ I ^ n) :
    x = 0 :=
  IsHausdorff.haus ‹_› x fun n ↦ by
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_top_eq_self]; exact hx n

variable (I) in
/-- In a ring that is Hausdorff for the `I`-adic filtration, a nonzero element has a
well-defined `I`-adic order: it lies in `I ^ n` but not in `I ^ (n + 1)` for exactly one `n`. -/
theorem IsHausdorff.exists_mem_pow_and_notMem_pow_succ [IsHausdorff I R] {x : R} (hx : x ≠ 0) :
    ∃ n, x ∈ I ^ n ∧ x ∉ I ^ (n + 1) := by
  classical
  have hnot : ∃ n, x ∉ I ^ n := by
    by_contra! hall
    exact hx (eq_zero_of_forall_mem_pow x hall)
  have hpos : Nat.find hnot ≠ 0 := fun h0 ↦ Nat.find_spec hnot (by rw [h0]; simp)
  exact ⟨Nat.find hnot - 1, not_not.mp (Nat.find_min hnot (by lia)),
    by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos)]; exact Nat.find_spec hnot⟩

/-! ### Adic completeness only depends on the ideal up to taking powers -/

/-- Adic completeness of a module transfers between ideals squeezed between powers of each
other: if `I ≤ J` and `J ^ e ≤ I`, the two filtrations are cofinal, so `I`-adic completeness
gives `J`-adic completeness. This is the module-level twin of `IsAdic.of_le_of_pow_le`, which
says the same for the topologies. -/
theorem isAdicComplete_of_le_of_pow_le {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {I J : Ideal A} {e : ℕ} (he : 0 < e) (hIJ : I ≤ J) (hJI : J ^ e ≤ I) [IsAdicComplete I M] :
    IsAdicComplete J M := by
  have hJI' (n : ℕ) : (J ^ (e * n) • ⊤ : Submodule A M) ≤ I ^ n • ⊤ :=
    Submodule.smul_mono_left (by rw [pow_mul]; exact Ideal.pow_right_mono hJI n)
  have hIJ' (n : ℕ) : (I ^ n • ⊤ : Submodule A M) ≤ J ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff J M :=
    ⟨fun x hx ↦ IsHausdorff.haus ‹IsAdicComplete I M›.toIsHausdorff x fun n ↦
      SModEq.mono (hJI' n) (hx (e * n))⟩
  have hP : IsPrecomplete J M := by
    refine ⟨fun {f} hf ↦ ?_⟩
    have hcau : ∀ {m n}, m ≤ n → f (e * m) ≡ f (e * n) [SMOD (I ^ m • ⊤ : Submodule A M)] :=
      fun {m n} hmn ↦ SModEq.mono (hJI' m) (hf (Nat.mul_le_mul_left e hmn))
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsAdicComplete I M›.toIsPrecomplete hcau
    refine ⟨L, fun n ↦ ?_⟩
    have h1 : f n ≡ f (e * n) [SMOD (J ^ n • ⊤ : Submodule A M)] :=
      hf (Nat.le_mul_of_pos_left n he)
    exact h1.trans (SModEq.mono (hIJ' n) (hL n))
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

/-- `J^e`-adic completeness of a module implies `J`-adic completeness (the filtrations are
cofinal). -/
theorem isAdicComplete_of_pow {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {J : Ideal A} {e : ℕ} (he : 0 < e) [IsAdicComplete (J ^ e) M] : IsAdicComplete J M :=
  isAdicComplete_of_le_of_pow_le he (Ideal.pow_le_self he.ne') le_rfl

/-! ### Quotients by idempotents, and lifting idempotents -/

/-- **Adic completeness passes to the quotient by an idempotent**: for an idempotent `ε`,
the quotient `A ⧸ (1 - ε)` (the corner `εA`) is complete for the image filtration. The
idempotent trivializes both halves: multiplication by `ε` projects any lift into a coherent
one, and kills the ambiguity `(1 - ε)A`. -/
theorem IsIdempotentElem.isAdicComplete_quotient {A : Type*} [CommRing A] {ε : A}
    (hε : IsIdempotentElem ε) (I : Ideal A) [IsAdicComplete I A] :
    IsAdicComplete (I.map (Ideal.Quotient.mk (Ideal.span {1 - ε})))
      (A ⧸ Ideal.span {1 - ε}) := by
  set mk := Ideal.Quotient.mk (Ideal.span {1 - ε})
  have hmkε : mk ε = 1 := Ideal.Quotient.mk_span_one_sub ε
  have hH : IsHausdorff (I.map mk) (A ⧸ Ideal.span {1 - ε}) := by
    refine ⟨fun x hx ↦ ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {1 - ε}) x
    have hεr : ε * r = 0 :=
      IsHausdorff.eq_zero_of_forall_mem_pow (I := I) _ fun n ↦
        hε.mul_mem_pow_of_mk_mem_map_pow I
          (by simpa [SModEq.zero, Ideal.smul_top_eq_self] using hx n)
    rw [show mk r = mk (ε * r) by rw [map_mul, hmkε, one_mul], hεr, map_zero]
  have hP : IsPrecomplete (I.map mk) (A ⧸ Ideal.span {1 - ε}) := by
    refine ⟨fun {f} hf ↦ ?_⟩
    choose r hr using fun n ↦ Ideal.Quotient.mk_surjective (I := Ideal.span {1 - ε}) (f n)
    have hcau : ∀ {m n}, m ≤ n → ε * r m ≡ ε * r n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at h ⊢
      rw [← mul_sub]
      exact hε.mul_mem_pow_of_mk_mem_map_pow I (by rw [map_sub, hr, hr]; exact h)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsAdicComplete I A›.toIsPrecomplete hcau
    refine ⟨mk L, fun n ↦ ?_⟩
    have h2 := hL n
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at h2 ⊢
    rw [show f n = mk (ε * r n) by rw [map_mul, hmkε, one_mul, hr], ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h2
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

/-- **Idempotents lift along an adically complete ideal.** If `a` is idempotent modulo an
`I`-adically complete ideal `I` (`a² - a ∈ I`), the Newton iteration `x ↦ 3x² - 2x³` converges
to an exact idempotent of the ring congruent to `a` modulo `I`. -/
theorem IsAdicComplete.exists_isIdempotentElem_of_sq_sub_mem {A : Type*} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] {a : A} (ha : a ^ 2 - a ∈ I) :
    ∃ e : A, IsIdempotentElem e ∧ e - a ∈ I := by
  set w : ℕ → A := fun n ↦ Nat.rec a (fun _ x ↦ 3 * x ^ 2 - 2 * x ^ 3) n
  have hw0 : w 0 = a := rfl
  have hws : ∀ k, w (k + 1) = 3 * w k ^ 2 - 2 * w k ^ 3 := fun _ ↦ rfl
  have hkey : ∀ k, w k ^ 2 - w k ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [hw0] using ha
    | succ k ih =>
      have hident : w (k + 1) ^ 2 - w (k + 1)
          = (w k ^ 2 - w k) ^ 2 * (-(3 - 2 * w k) * (1 + 2 * w k)) := by
        rw [hws]; ring
      rw [hident]
      have h2 : (w k ^ 2 - w k) ^ 2 ∈ I ^ (k + 1) * I ^ (k + 1) := by
        rw [sq]; exact Ideal.mul_mem_mul ih ih
      rw [← pow_add] at h2
      exact Ideal.pow_le_pow_right (by lia) (Ideal.mul_mem_right _ _ h2)
  have hstep : ∀ k, w (k + 1) - w k ∈ I ^ (k + 1) := by
    intro k
    have hident : w (k + 1) - w k = -(2 * w k - 1) * (w k ^ 2 - w k) := by rw [hws]; ring
    rw [hident]
    exact Ideal.mul_mem_left _ _ (hkey k)
  obtain ⟨z, hz0, hzn⟩ := IsPrecomplete.exists_limit w hstep
  have hzid : z ^ 2 - z = 0 := by
    refine IsHausdorff.eq_zero_of_forall_mem_pow (I := I) _ fun n ↦ ?_
    have hident : z ^ 2 - z = (z - w n) * (z + w n - 1) + (w n ^ 2 - w n) := by ring
    rw [hident]
    exact add_mem (Ideal.mul_mem_right _ _ (hzn n))
      (Ideal.pow_le_pow_right (by lia) (hkey n))
  exact ⟨z, by rw [IsIdempotentElem]; linear_combination hzid, hw0 ▸ hz0⟩

/-! ### Modules with a finite basis -/

section AdicBasis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A module with a finite basis over an `I`-adically complete ring is `I`-adically
complete. -/
theorem Module.Basis.isAdicComplete {I : Ideal R} {ι : Type*} [Finite ι]
    (b : Module.Basis ι R M) [IsAdicComplete I R] : IsAdicComplete I M where
  haus' x hx := by
    have h (i : ι) : b.repr x i = 0 := by
      refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff : IsHausdorff I R) _ fun n ↦ ?_
      rw [SModEq.zero, Ideal.smul_top_eq_self]
      have hxn := hx n
      rw [SModEq.zero] at hxn
      exact (b.mem_smul_top_iff _ x).mp hxn i
    have hrepr : b.repr x = 0 := Finsupp.ext h
    simpa using congrArg b.repr.symm hrepr
  prec' f hf := by
    let : Fintype ι := Fintype.ofFinite ι
    have hcoord (i : ι) :
        ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
      refine IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete : IsPrecomplete I R)
        fun {m n} hmn ↦ ?_
      have hmem := hf hmn
      rw [SModEq.sub_mem] at hmem ⊢
      rw [Ideal.smul_top_eq_self, ← Finsupp.sub_apply, ← map_sub]
      exact (b.mem_smul_top_iff _ _).mp hmem i
    choose L hL using hcoord
    refine ⟨∑ i, L i • b i, fun n ↦ ?_⟩
    rw [SModEq.sub_mem, b.mem_smul_top_iff]
    intro i
    have hLn := hL i n
    rw [SModEq.sub_mem, Ideal.smul_top_eq_self] at hLn
    have hrepr : b.repr (∑ j, L j • b j) i = L i := by
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
        mul_one, Finsupp.finsetSum_apply]
      exact (Finset.sum_eq_single (f := fun c ↦ (Finsupp.single c (L c)) i) i
        (fun c _ hc ↦ Finsupp.single_eq_of_ne hc.symm)
        (fun h ↦ absurd (Finset.mem_univ i) h)).trans Finsupp.single_eq_same
    rwa [map_sub, Finsupp.sub_apply, hrepr]

end AdicBasis

end
