/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.RingTheory.Flat.Basic`: the rank of a module, for the statement.
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Rank monotonicity under flat base change

For a flat `R`-algebra `S`, an injective `R`-linear map `M →ₗ[R] N` gives
`rank S (S ⊗ M) ≤ rank S (S ⊗ N)`: flatness keeps the base-changed map injective. With `R = ℤ`
and `S = ℚ` this says that the rational rank of an abelian group is monotone in subgroups.

## Main statements

* `LinearMap.rank_baseChange_le_of_injective`: base change along a flat algebra does not decrease
  the rank of the source of an injective linear map.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

open TensorProduct

universe u

/-- Base change along a flat algebra does not decrease the rank of the source of an
injective linear map. -/
theorem LinearMap.rank_baseChange_le_of_injective {R : Type*} (S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] {M N : Type u} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] {f : M →ₗ[R] N} (hf : Function.Injective f) :
    Module.rank S (S ⊗[R] M) ≤ Module.rank S (S ⊗[R] N) :=
  (f.baseChange S).rank_le_of_injective
    (by rw [baseChange_eq_lTensor]; exact Module.Flat.lTensor_preserves_injective_linearMap f hf)

end
