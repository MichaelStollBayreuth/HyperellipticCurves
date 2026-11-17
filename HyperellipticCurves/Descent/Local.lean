/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.JacobianStructure
public import HyperellipticCurves.Descent.Map
public import HyperellipticCurves.Descent.Selmer
public import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.AdicValuation

import HyperellipticCurves.Descent.Image
import HyperellipticCurves.Descent.Kernel
import HyperellipticCurves.Descent.Semilocal
import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Local conditions, the `2`-Selmer group and the relaxed Selmer groups

Let `f : K[X]` be squarefree of odd degree and `L = K[X] / (f)`. For a field extension `F` of `K`,
the local condition at `F` consists of the classes in `L^× / (L^×)^2` whose image over `F` lies in
the image of the `x - T` map `μ_F` over `F`. The `2`-Selmer group, relative to a Dedekind domain
`R` with fraction field `K` of characteristic `0` and a family of further field extensions of `K`
(for a number field, the completions at the infinite places), consists of the classes of norm a
square that satisfy the local conditions at all completions and at the members of the family. The
relaxed Selmer group `S(S, Loc)` consists of the classes of `A(S, 2)` (`AdjoinRoot.selmerGroup`)
of norm a square that satisfy the local conditions at the members of a family `Loc` only. Both
contain the image of `μ`, and a finite one bounds the rank of `J(K)`.

## Main definitions

* `ChabautyColeman.HypJac.localCondition`: the local condition at a field extension of `K`.
* `ChabautyColeman.HypJac.selmerGroupTwo`: the `2`-Selmer group.
* `ChabautyColeman.relaxedSelmerGroup`: the relaxed Selmer group `S(S, Loc)`.

## Main statements

* `ChabautyColeman.HypJac.range_descentMap_le_selmerGroupTwo`: `μ(J(K))` lies in the `2`-Selmer
  group.
* `ChabautyColeman.HypJac.selmerGroupTwo_le_selmerGroup`,
  `ChabautyColeman.HypJac.finite_selmerGroupTwo`: the `2`-Selmer group lies in `A(S, 2)` when `f`
  has separable reduction outside `S`, and it is finite;
  `ChabautyColeman.HypJac.pow_rank_le_card_selmerGroupTwo`: the rank bound.
* `ChabautyColeman.HypJac.LocalStructure.range_descentMap_eq_of_le_of_card_ge`: over a `p`-adic
  field, `p ≠ 2`, a subgroup of `μ(J(F))` with at least `#J(F)[2]` elements is all of it.
* `ChabautyColeman.range_descentMap_le_relaxedSelmerGroup`: `μ(J(K))` lies in `S(S, Loc)` if `f`
  has separable reduction outside `S`.
* `ChabautyColeman.finite_relaxedSelmerGroup`,
  `ChabautyColeman.pow_rank_le_card_relaxedSelmerGroup`: `S(S, Loc)` is finite for finite `S` over a
  number field, and the rank bound.

## Implementation notes

The local conditions are taken at arbitrary field extensions of `K`, so that the relaxed Selmer
group can use `ℚ_[2]` itself as the `2`-adic field of `ℚ`.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5
-/

@[expose] public section

open Polynomial IsDedekindDomain

/-! ### The local conditions -/

namespace ChabautyColeman

section LocalCondition

variable {K : Type*} [Field K] (f : K[X]) [Fact (Odd f.natDegree)] (F : Type*) [Field F]
  [Algebra K F] [NeZero (2 : F)] [Fact (Squarefree (f.map (algebraMap K F)))]

/-- The local condition of `2`-descent at a field extension `F` of `K` (in the applications a
completion of `K`): the classes in `L^× / (L^×)^2`, `L = K[X] / (f)`, whose image in
`F[X] / (f)` lies in the image of the `x - T` map over `F`. -/
noncomputable def HypJac.localCondition : Subgroup (Units.ModPow (AdjoinRoot f) 2) :=
  (descentMap (f.map (algebraMap K F))).range.comap
    (Units.ModPow.map (AdjoinRoot.map (algebraMap K F) f (f.map (algebraMap K F)) dvd_rfl) 2)

theorem HypJac.mem_localCondition_iff {x : Units.ModPow (AdjoinRoot f) 2} :
    x ∈ localCondition f F ↔
      Units.ModPow.map (AdjoinRoot.map (algebraMap K F) f (f.map (algebraMap K F)) dvd_rfl) 2 x ∈
        (descentMap (f.map (algebraMap K F))).range :=
  Subgroup.mem_comap

variable [NeZero (2 : K)] [Fact (Squarefree f)]

/-- The image of the `x - T` map satisfies every local condition, by base change
(`ChabautyColeman.HypJac.map_descentMap`). -/
theorem HypJac.range_descentMap_le_localCondition : (descentMap f).range ≤ localCondition f F := by
  rintro _ ⟨x, rfl⟩
  exact ⟨HypJac.map f x, (map_descentMap f x).symm⟩

theorem HypJac.range_descentMap_le_ker_norm :
    (descentMap f).range ≤ (Units.ModPow.map (Algebra.norm K) 2).ker := by
  rintro _ ⟨x, rfl⟩
  exact descentMap_mem_ker_norm f x

end LocalCondition

section SelmerGroupTwo

variable {K : Type*} [Field K] [CharZero K] (f : K[X]) [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)] (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K] {ι : Type*} (Loc : ι → Type*) [(i : ι) → Field (Loc i)]
  [(i : ι) → Algebra K (Loc i)] [(i : ι) → NeZero (2 : Loc i)]

/-- The **`2`-Selmer group** of the Jacobian of `y ^ 2 = f(x)`, relative to a Dedekind domain `R`
with fraction field `K` and a family `Loc` of field extensions of `K`: the classes in
`L^× / (L^×)^2`, `L = K[X] / (f)`, of norm a square that satisfy the local conditions
(`ChabautyColeman.HypJac.localCondition`) at the completions of `K` at the primes of `R` and at
the members of `Loc`. For a number field `K`, `R = 𝓞 K` and `Loc` the completions at the infinite
places, this is the classical `2`-Selmer group. -/
noncomputable def HypJac.selmerGroupTwo : Subgroup (Units.ModPow (AdjoinRoot f) 2) :=
  (Units.ModPow.map (Algebra.norm K) 2).ker ⊓
    (⨅ v : HeightOneSpectrum R, localCondition f (v.adicCompletion K)) ⊓
      ⨅ i, localCondition f (Loc i)

theorem HypJac.mem_selmerGroupTwo_iff {x : Units.ModPow (AdjoinRoot f) 2} :
    x ∈ selmerGroupTwo f R Loc ↔ Units.ModPow.map (Algebra.norm K) 2 x = 1 ∧
      (∀ v : HeightOneSpectrum R, x ∈ localCondition f (v.adicCompletion K)) ∧
        ∀ i, x ∈ localCondition f (Loc i) := by
  simp [selmerGroupTwo, Subgroup.mem_iInf, and_assoc]

/-- The image of the `x - T` map lies in the `2`-Selmer group: it satisfies the norm condition
and every local condition. -/
theorem HypJac.range_descentMap_le_selmerGroupTwo :
    (descentMap f).range ≤ selmerGroupTwo f R Loc :=
  le_inf (le_inf (range_descentMap_le_ker_norm f)
    (le_iInf fun _ ↦ range_descentMap_le_localCondition f _))
      (le_iInf fun _ ↦ range_descentMap_le_localCondition f _)

theorem HypJac.selmerGroupTwo_le_ker_norm :
    selmerGroupTwo f R Loc ≤ (Units.ModPow.map (Algebra.norm K) 2).ker :=
  inf_le_left.trans inf_le_left

variable {f R} in
/-- The `2`-Selmer group consists of classes unramified outside every set `S` of primes outside
which `f` has separable reduction: at `v ∉ S`, the local condition at `K_v` puts the class into
the image of the `x - T` map over `K_v`, which consists of unramified classes by
`ChabautyColeman.HypJac.range_descentMap_le_selmerGroup` over the completion `𝒪_v`, and
`AdjoinRoot.mem_selmerGroup_of_forall_adicCompletion` passes from `K_v` to `K`. -/
theorem HypJac.selmerGroupTwo_le_selmerGroup {S : Set (HeightOneSpectrum R)}
    (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K)) :
    selmerGroupTwo f R Loc ≤ AdjoinRoot.selmerGroup Fact.out S 2 := fun _ hx ↦
  AdjoinRoot.mem_selmerGroup_of_forall_adicCompletion Fact.out fun v hv ↦
    range_descentMap_le_selmerGroup (f.map _) (R := v.adicCompletionIntegers K) (S := ∅)
      (fun P _ ↦ (hS v hv).map fun c hc ↦ (v.valuation_adicCompletion_algebraMap P c).trans_le hc)
      ((mem_localCondition_iff ..).mp (((mem_selmerGroupTwo_iff ..).mp hx).2.1 v))

/-- The `2`-Selmer group is finite: by `ChabautyColeman.HypJac.selmerGroupTwo_le_selmerGroup` it
lies in `A(S, 2)` for the set `S` of primes at which `f` does not have separable reduction, which
is finite (`Polynomial.finite_setOf_not_hasSeparableReduction`). -/
theorem HypJac.finite_selmerGroupTwo
    [∀ p : f.Factors, Finite (ClassGroup (integralClosure R (AdjoinRoot (p : K[X]))))]
    [∀ p : f.Factors, IsMulFG (integralClosure R (AdjoinRoot (p : K[X])))ˣ] :
    Finite (selmerGroupTwo f R Loc) :=
  have := AdjoinRoot.finite_selmerGroup (f := f) Fact.out
    (finite_setOf_not_hasSeparableReduction (R := R) (Fact.out : Squarefree f).ne_zero
      (discr_ne_zero_of_isCoprime_derivative (PerfectField.separable_iff_squarefree.mpr Fact.out)))
    2
  .of_injective _ (Subgroup.inclusion_injective (selmerGroupTwo_le_selmerGroup Loc
    (S := {v | ¬ f.HasSeparableReduction (v.valuation K)}) fun _ ↦ not_not.mp))

/-- **The rank bound** of `2`-descent from the `2`-Selmer group: for `J(K)` finitely generated of
rank `r`, `2 ^ r * #J(K)[2] ≤ #Sel₂`. -/
theorem HypJac.pow_rank_le_card_selmerGroupTwo [IsMulFG (HypJac K f)]
    [∀ p : f.Factors, Finite (ClassGroup (integralClosure R (AdjoinRoot (p : K[X]))))]
    [∀ p : f.Factors, IsMulFG (integralClosure R (AdjoinRoot (p : K[X])))ˣ] :
    2 ^ Module.finrank ℤ (Additive (HypJac K f)) *
        Nat.card (powMonoidHom 2 : HypJac K f →* HypJac K f).ker ≤
      Nat.card (selmerGroupTwo f R Loc) :=
  have := finite_selmerGroupTwo f R Loc
  pow_rank_le_card_of_range_descentMap_le f (range_descentMap_le_selmerGroupTwo f R Loc)

end SelmerGroupTwo

section LocalImage

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Algebra ℚ_[p] F] [NeZero (2 : F)]
  {f : F[X]} [Fact (Odd f.natDegree)] [Fact (Squarefree f)] {g : ℕ}

/-- **The image of the `x - T` map over a `p`-adic field**, `p ≠ 2`: under the cited structure of
`J(F)`, it has `#J(F)[2]` elements (`ChabautyColeman.HypJac.card_range_descentMap_eq_card_quotient`
and `ChabautyColeman.HypJac.LocalStructure.card_modPow_two_of_ne_two`), so a subgroup of it with
at least as many elements is all of it. -/
theorem HypJac.LocalStructure.range_descentMap_eq_of_le_of_card_ge (L : LocalStructure p F f g)
    (hp : p ≠ 2) {H : Subgroup (Units.ModPow (AdjoinRoot f) 2)} (hH : H ≤ (descentMap f).range)
    (hcard : Nat.card (powMonoidHom 2 : HypJac F f →* HypJac F f).ker ≤ Nat.card H) :
    (descentMap f).range = H := by
  have hc := (card_range_descentMap_eq_card_quotient f).trans (L.card_modPow_two_of_ne_two hp)
  have : Finite (descentMap f).range :=
    Nat.finite_of_card_ne_zero (by rw [hc, card_ker_powMonoidHom_two]; positivity)
  exact (Subgroup.eq_of_le_of_card_ge hH (hc.trans_le hcard)).symm

end LocalImage

end ChabautyColeman

/-! ### The relaxed Selmer groups -/

namespace ChabautyColeman

variable {K : Type*} [Field K] (f : K[X]) [Fact (Odd f.natDegree)] [Fact (Squarefree f)]
  [PerfectField K] {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Algebra R K] [IsFractionRing R K] (S : Set (HeightOneSpectrum R)) {ι : Type*}
  (Loc : ι → Type*) [(i : ι) → Field (Loc i)] [(i : ι) → Algebra K (Loc i)]
  [(i : ι) → NeZero (2 : Loc i)]

/-- The **relaxed Selmer group** `S(S, Loc)`: the classes of `A(S, 2)` (`AdjoinRoot.selmerGroup`) of
norm a square that satisfy the local conditions (`ChabautyColeman.HypJac.localCondition`) at the
members of the family `Loc` of field extensions of `K` only. It contains the image of the `x - T`
map (`ChabautyColeman.range_descentMap_le_relaxedSelmerGroup`) when `f` has separable reduction
outside `S`. -/
noncomputable def relaxedSelmerGroup : Subgroup (Units.ModPow (AdjoinRoot f) 2) :=
  AdjoinRoot.selmerGroup Fact.out S 2 ⊓ (Units.ModPow.map (Algebra.norm K) 2).ker ⊓
    ⨅ i, HypJac.localCondition f (Loc i)

variable {S} in
theorem finite_relaxedSelmerGroup (hS : S.Finite)
    [∀ p : f.Factors, Finite (ClassGroup (integralClosure R (AdjoinRoot (p : K[X]))))]
    [∀ p : f.Factors, IsMulFG (integralClosure R (AdjoinRoot (p : K[X])))ˣ] :
    Finite (relaxedSelmerGroup f S Loc) :=
  have := AdjoinRoot.finite_selmerGroup (f := f) Fact.out hS 2
  .of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans inf_le_left))

variable [NeZero (2 : K)]

variable {f S} in
theorem range_descentMap_le_relaxedSelmerGroup
    (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K)) :
    (HypJac.descentMap f).range ≤ relaxedSelmerGroup f S Loc :=
  le_inf (le_inf (HypJac.range_descentMap_le_selmerGroup f hS)
    (HypJac.range_descentMap_le_ker_norm f)) (le_iInf fun _ ↦
      HypJac.range_descentMap_le_localCondition f _)

variable {f S} in
/-- **The rank bound** of `2`-descent from a relaxed Selmer group: for `J(K)` finitely generated
of rank `r`, `2 ^ r * #J(K)[2] ≤ #S(S, Loc)`. -/
theorem pow_rank_le_card_relaxedSelmerGroup [IsMulFG (HypJac K f)]
    (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K)) (hSf : S.Finite)
    [∀ p : f.Factors, Finite (ClassGroup (integralClosure R (AdjoinRoot (p : K[X]))))]
    [∀ p : f.Factors, IsMulFG (integralClosure R (AdjoinRoot (p : K[X])))ˣ] :
    2 ^ Module.finrank ℤ (Additive (HypJac K f)) *
        Nat.card (powMonoidHom 2 : HypJac K f →* HypJac K f).ker ≤
      Nat.card (relaxedSelmerGroup f S Loc) :=
  have := finite_relaxedSelmerGroup f Loc hSf
  HypJac.pow_rank_le_card_of_range_descentMap_le f (range_descentMap_le_relaxedSelmerGroup Loc hS)

end ChabautyColeman

end
