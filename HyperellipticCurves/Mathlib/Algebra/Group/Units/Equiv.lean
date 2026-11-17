/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Units.Equiv

/-!
# The additive version of `Units.mapEquiv`

Mathlib PR #44614 (`Units.ModPow`) tags `Units.mapEquiv`, `Units.mapEquiv_symm` and
`Units.coe_mapEquiv` with `to_additive` in the sibling file, for the additive version
`AddUnits.ModNSMul.congr` of `Units.ModPow.congr`. Until the PR is merged, the additive versions
are declared here by hand and registered with `to_additive existing`: in a module, `to_additive`
cannot translate a declaration of another module after the fact.
-/

@[expose] public section

namespace AddUnits

variable {M N : Type*} [AddMonoid M] [AddMonoid N]

/-- An additive equivalence of additive monoids defines an additive equivalence of their groups of
additive units. -/
def mapEquiv (h : M ≃+ N) : AddUnits M ≃+ AddUnits N :=
  { map h.toAddMonoidHom with
    invFun := map h.symm.toAddMonoidHom
    left_inv := fun u ↦ ext <| h.left_inv u
    right_inv := fun u ↦ ext <| h.right_inv u }

@[simp]
theorem mapEquiv_symm (h : M ≃+ N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl

@[simp]
theorem coe_mapEquiv (h : M ≃+ N) (x : AddUnits M) : (mapEquiv h x : N) = h x :=
  rfl

end AddUnits

attribute [to_additive existing] Units.mapEquiv Units.mapEquiv_symm Units.coe_mapEquiv
