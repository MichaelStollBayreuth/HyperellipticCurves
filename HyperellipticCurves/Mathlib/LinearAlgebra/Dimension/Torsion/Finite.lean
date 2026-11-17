/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

-- Beyond the sibling: rank-nullity over a domain, and finite groups are torsion.
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Torsion factors of a product do not contribute to the rank

## Main statements

* `Module.rank_prod_of_isTorsion_right`: over a domain, `rank (M × T) = rank M` for a torsion
  module `T`.
* `Module.finrank_prod_of_finite_right`: a finite factor does not contribute to the rank over `ℤ`
  of a product of additive groups.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/SelmerGroup.lean`, there for `ℤ` and a
finite factor); upstreaming candidates for Mathlib.
-/

@[expose] public section

universe u

namespace Module

/-- A torsion factor does not contribute to the rank of a product over a domain: the kernel of the
first projection is the torsion factor, of rank `0` (`Module.IsTorsion.rank_eq_zero`). -/
theorem rank_prod_of_isTorsion_right {R : Type*} {M T : Type u} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup T] [Module R T] (hT : IsTorsion R T) :
    Module.rank R (M × T) = Module.rank R M := by
  rw [← (LinearMap.fst R M T).rank_range_add_rank_ker, LinearMap.ker_fst,
    ← (LinearEquiv.ofInjective _ LinearMap.inr_injective).rank_eq, hT.rank_eq_zero, add_zero,
    LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top]

/-- `Module.rank_prod_of_isTorsion_right` for `finrank` over `ℤ` and a finite factor. -/
theorem finrank_prod_of_finite_right (M T : Type u) [AddCommGroup M] [AddCommGroup T] [Finite T] :
    finrank ℤ (M × T) = finrank ℤ M :=
  congr(Cardinal.toNat $(rank_prod_of_isTorsion_right (M := M) (T := T)
    (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite)))

end Module
