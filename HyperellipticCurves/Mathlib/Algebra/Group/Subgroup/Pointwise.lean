/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

import HyperellipticCurves.Mathlib.Algebra.Group.Pointwise.Set.Lattice

/-!
# The supremum of a finite normal subgroup and an intersection of subgroups

In a coframe, `sup_iInf_eq` says that `a ⊔ ⨅ i, f i = ⨅ i, a ⊔ f i`. The lattice of subgroups of a
group is not a coframe, but the equality holds for a finite normal subgroup and a family of
subgroups that is directed downward, since the supremum with a normal subgroup is the product of
sets (`Subgroup.normal_mul`).

## Main statements

* `Subgroup.sup_iInf_eq_of_directed`: `H ⊔ ⨅ i, K i = ⨅ i, H ⊔ K i` for a finite normal subgroup
  `H` and a family `K` of subgroups that is directed downward.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The form of `sup_iInf_eq` for a finite normal subgroup `H` and a family `K` of subgroups that
is directed downward, by `Set.Finite.mul_iInter_of_directed`. -/
@[to_additive /-- The form of `sup_iInf_eq` for a finite normal additive subgroup `H` and a family
`K` of additive subgroups that is directed downward, by `Set.Finite.add_iInter_of_directed`. -/]
theorem sup_iInf_eq_of_directed {ι : Sort*} {H : Subgroup G} [H.Normal] [Finite H]
    {K : ι → Subgroup G} (hK : Directed (· ≥ ·) K) :
    H ⊔ ⨅ i, K i = ⨅ i, H ⊔ K i := by
  cases isEmpty_or_nonempty ι
  · simp
  exact SetLike.coe_injective <| by
    simpa only [normal_mul, coe_iInf] using (Set.toFinite (H : Set G)).mul_iInter_of_directed hK

end Subgroup
