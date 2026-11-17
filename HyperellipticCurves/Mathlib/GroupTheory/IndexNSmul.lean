/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: the characteristic and the units modulo `n`-th powers in the statement of
-- `Units.card_modPow_two`, and for the proofs the structure theorem for finitely generated abelian
-- groups, the roots of unity of order `2`, isomorphisms on kernels and the rank of a product with a
-- finite factor.
public import HyperellipticCurves.Mathlib.GroupTheory.QuotientGroup.UnitsModPow
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.IndexNSmul

import HyperellipticCurves.Mathlib.Algebra.Group.Subgroup.Ker
import HyperellipticCurves.Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The index of `n • G` in a finitely generated abelian group

## Main statements

* `AddSubgroup.index_range_nsmul_of_isAddFG`: for a finitely generated abelian group `G` and
  `n ≠ 0`, the index of `n • G` is `n ^ rank G * #G[n]`, where `G[n]` is the kernel of
  multiplication by `n`.
* `CommGroup.card_modPow`: the multiplicative version, `#(G / Gⁿ) = n ^ rank G * #G[n]`.
* `AddSubgroup.index_range_nsmul_prod_of_injective`: the index of `n • (M × T)` for `T` finite and
  `M` without `n`-torsion is the index of `n • M` times `#(M × T)[n]`.
* `Units.card_modPow_two`: `#(Rˣ / (Rˣ)²) = 2 ^ (rank Rˣ + 1)` for a domain `R` of characteristic
  `≠ 2` with finitely generated unit group.
* `Subgroup.card_ker_powMonoidHom`: the elements of order dividing `n` of a subgroup `B` are those
  of `B ⊓ G[n]`.
* `Subgroup.card_map_le_card_inf_ker_powMonoidHom`: a homomorphism to a group of exponent `n`
  maps a finite subgroup `B` onto a group of order at most `#B[n]`.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/SelmerGroup.lean`), for the rank formula of
the `2`-descent on hyperelliptic Jacobians; upstreaming candidates for Mathlib.
-/

@[expose] public section

universe u

open Module

section AddCommGroup

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

theorem AddEquiv.card_ker_nsmulAddMonoidHom (e : M ≃+ N) (n : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := M) n).ker = Nat.card (nsmulAddMonoidHom (α := N) n).ker := by
  rw [← e.map_ker_nsmulAddMonoidHom n]
  exact Nat.card_congr (AddSubgroup.equivMapOfInjective _ (e : M →+ N) e.injective).toEquiv

/-- The index of `n • G` is invariant under additive equivalence. -/
theorem AddEquiv.index_range_nsmulAddMonoidHom (e : M ≃+ N) (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index = (nsmulAddMonoidHom (α := N) n).range.index := by
  simpa [AddEquiv.map_range_nsmulAddMonoidHom]
    using (AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := M) n).range e).symm

variable (M N) in
theorem nsmulAddMonoidHom_range_prod (n : ℕ) :
    (nsmulAddMonoidHom (α := M × N) n).range =
      ((nsmulAddMonoidHom (α := M) n).range).prod (nsmulAddMonoidHom (α := N) n).range :=
  AddMonoidHom.range_prodMap (nsmulAddMonoidHom (α := M) n) (nsmulAddMonoidHom (α := N) n)

variable (M N) in
theorem nsmulAddMonoidHom_ker_prod (n : ℕ) :
    (nsmulAddMonoidHom (α := M × N) n).ker =
      ((nsmulAddMonoidHom (α := M) n).ker).prod (nsmulAddMonoidHom (α := N) n).ker :=
  AddMonoidHom.ker_prodMap (nsmulAddMonoidHom (α := M) n) (nsmulAddMonoidHom (α := N) n)

variable (M) in
theorem nsmulAddMonoidHom_range_pi (ι : Type*) (n : ℕ) :
    (nsmulAddMonoidHom (α := ι → M) n).range =
      AddSubgroup.pi Set.univ fun _ ↦ (nsmulAddMonoidHom (α := M) n).range := by
  ext x
  simp [funext_iff, AddSubgroup.mem_pi, Classical.skolem]

end AddCommGroup

/-- The index of `n • (M × T)` for `T` finite and `M` without `n`-torsion. -/
theorem AddSubgroup.index_range_nsmul_prod_of_injective {M T : Type*} [AddCommGroup M]
    [AddCommGroup T] [Finite T] {n : ℕ} (hM : Function.Injective (nsmulAddMonoidHom (α := M) n)) :
    (nsmulAddMonoidHom (α := M × T) n).range.index =
      (nsmulAddMonoidHom (α := M) n).range.index *
        Nat.card (nsmulAddMonoidHom (α := M × T) n).ker := by
  rw [nsmulAddMonoidHom_range_prod, index_prod, index_range (f := nsmulAddMonoidHom (α := T) n),
    nsmulAddMonoidHom_ker_prod, Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
    (AddMonoidHom.ker_eq_bot_iff _).mpr hM]
  simp

theorem AddSubgroup.index_range_nsmul_pi {ι M : Type*} [Fintype ι] [AddCommGroup M] (n : ℕ) :
    (nsmulAddMonoidHom (α := ι → M) n).range.index =
      (nsmulAddMonoidHom (α := M) n).range.index ^ Fintype.card ι := by
  rw [nsmulAddMonoidHom_range_pi, index_pi, Finset.prod_const, Finset.card_univ]

/-- The index of `n • G` for `G = M × T` with `M` free of finite rank and `T` finite. -/
theorem AddSubgroup.index_range_nsmul_prod_of_finite (M T : Type u) [AddCommGroup M]
    [AddCommGroup T] [Free ℤ M] [Module.Finite ℤ M] [Finite T] {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := M × T) n).range.index =
      n ^ finrank ℤ (M × T) * Nat.card (nsmulAddMonoidHom (α := M × T) n).ker := by
  rw [finrank_prod_of_finite_right, index_range_nsmul_prod_of_injective
    (nsmulAddMonoidHom_injective_of_isTorsionFree hn), index_range_nsmul]

/-- **The index of `n • G` in a finitely generated commutative group** `G` is
`n ^ rank G * #G[n]`, where `G[n]` is the `n`-torsion subgroup. This extends
`AddSubgroup.index_range_nsmul` (the free case) to arbitrary finitely generated groups. -/
theorem AddSubgroup.index_range_nsmul_of_isAddFG (G : Type*) [AddCommGroup G] [IsAddFG G]
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  have (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have : Finite (DirectSum ι fun i ↦ ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  rw [eqv.index_range_nsmulAddMonoidHom, eqv.card_ker_nsmulAddMonoidHom,
    eqv.toIntLinearEquiv.finrank_eq]
  exact index_range_nsmul_prod_of_finite _ _ hn

/-- The order of the group of `n`-th power classes of a finitely generated commutative group
`G` is `n ^ rank G * #G[n]`; multiplicative version of
`AddSubgroup.index_range_nsmul_of_isAddFG`. -/
theorem CommGroup.card_modPow (G : Type*) [CommGroup G] [IsMulFG G] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (G ⧸ (powMonoidHom n : G →* G).range) =
      n ^ finrank ℤ (Additive G) * Nat.card (powMonoidHom n : G →* G).ker := by
  rw [← Subgroup.index_eq_card]
  exact AddSubgroup.index_range_nsmul_of_isAddFG (Additive G) hn

/-- The order of `Rˣ/(Rˣ)²` for a domain `R` of characteristic `≠ 2` with finitely generated
unit group: `2 ^ (r + 1)`, where `r` is the rank of `Rˣ`, as the units of square `1` are `±1`
(`IsPrimitiveRoot.neg_one`). -/
theorem Units.card_modPow_two {R : Type*} [CommRing R] [IsDomain R] [IsMulFG Rˣ]
    (h2 : ringChar R ≠ 2) :
    Nat.card (Units.ModPow R 2) = 2 ^ (finrank ℤ (Additive Rˣ) + 1) := by
  rw [Units.ModPow, CommGroup.card_modPow Rˣ two_ne_zero, ← rootsOfUnity_eq_ker,
    (IsPrimitiveRoot.neg_one _ h2).card_rootsOfUnity, pow_succ]

namespace Subgroup

variable {G H : Type*} [CommGroup G] [Group H]

/-- The elements of order dividing `n` of a subgroup `B` are those of `B ⊓ G[n]`. -/
theorem card_ker_powMonoidHom (B : Subgroup G) (n : ℕ) :
    Nat.card (powMonoidHom n : B →* B).ker =
      Nat.card (B ⊓ (powMonoidHom n : G →* G).ker : Subgroup G) := by
  rw [← Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, inf_subgroupOf_left]
  congr 2
  ext b
  simp [mem_subgroupOf, Subtype.ext_iff]

/-- A homomorphism `φ` to a group of exponent `n` maps a finite subgroup `B` of a commutative
group onto a group of order at most `#B[n]`: `φ` kills `Bⁿ`, and `#(B/Bⁿ) = #B[n]`. -/
theorem card_map_le_card_inf_ker_powMonoidHom {B : Subgroup G} [Finite B] {n : ℕ} (φ : G →* H)
    (hφ : ∀ h : H, h ^ n = 1) :
    Nat.card (B.map φ) ≤ Nat.card (B ⊓ (powMonoidHom n : G →* G).ker : Subgroup G) := by
  have hsq : (powMonoidHom n : B →* B).range ≤ (φ.comp B.subtype).ker := by
    rintro _ ⟨b, rfl⟩
    simp [hφ]
  have h1 := card_ker_mul_card_range (φ.comp B.subtype)
  rw [MonoidHom.range_comp, range_subtype] at h1
  refine card_ker_powMonoidHom B n ▸
    Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := (φ.comp B.subtype).ker))
  rw [h1, ← card_ker_mul_card_range (powMonoidHom n : B →* B), mul_comm]
  exact Nat.mul_le_mul_right _ (card_le_of_le hsq)

end Subgroup
