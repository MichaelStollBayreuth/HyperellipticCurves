/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Subgroups of finitely generated commutative groups

## Main statements

* `IsMulFG.of_moduleFinite_int`: a commutative group that is finitely generated as a `ℤ`-module
  is finitely generated.
* `Subgroup.isMulFG_of_commGroup`: a subgroup of a finitely generated commutative group is finitely
  generated.
* `Subgroup.finite_closure_of_isOfFinOrder`: finitely many elements of finite order in a
  commutative group generate a finite subgroup.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/SelmerGroup.lean`), for the finite
generation of the `S`-unit group; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- A commutative group that is finitely generated as a `ℤ`-module is finitely generated as a
group; the other direction is the instance `AddMonoid.FG.to_moduleFinite_int`. -/
theorem IsMulFG.of_moduleFinite_int {G : Type*} [CommGroup G]
    (h : Module.Finite ℤ (Additive G)) : IsMulFG G :=
  isAddFG_additive_iff.mp (Module.Finite.iff_addGroup_fg.mp h)

/-- A subgroup of a finitely generated commutative group is finitely generated, as `ℤ` is a
Noetherian ring. (The proof passes through `Additive G`, so `to_additive` cannot translate it.) -/
theorem Subgroup.isMulFG_of_commGroup {G : Type*} [CommGroup G] [IsMulFG G] (H : Subgroup G) :
    IsMulFG H :=
  IsMulFG.of_moduleFinite_int <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)

/-- In a commutative group, finitely many elements of finite order generate a finite subgroup
(`CommGroup.finite_of_fg_isMulTorsion`). -/
theorem Subgroup.finite_closure_of_isOfFinOrder {G : Type*} [CommGroup G] {s : Set G} [Finite s]
    (hs : ∀ g ∈ s, IsOfFinOrder g) : Finite (closure s) :=
  CommGroup.finite_of_fg_isMulTorsion _ fun x ↦
    Submonoid.isOfFinOrder_coe.mp ((closure_le (CommGroup.torsion G)).mpr hs x.2)
