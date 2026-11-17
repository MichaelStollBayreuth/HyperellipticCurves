/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The codimension of the common kernel of a family of linear functionals

Let `R` be a subfield of `L` and let `V` be an `L`-vector space. A linear map
`Ψ : Q →ₗ[R] Module.Dual L V` from a finite-dimensional `R`-vector space `Q` cannot separate the
points of `V` beyond `dim_R Q` dimensions: the `L`-span of the image of `Ψ` has `L`-dimension at
most the `R`-dimension of the image (`Submodule.finrank_span_le_finrank`), so the subspace
annihilated by it is cut out by at most `dim_R Q` functionals. This is the dimension count behind
the space of annihilating differentials in the Chabauty–Coleman method, where `R = ℚ`,
`L = ℚ_p`, and `Q` is the rationalized Mordell–Weil group.

## Main statements

* `Module.finrank_le_finrank_iInf_ker_add_finrank`: the subspace `⨅ q, LinearMap.ker (Ψ q)` has
  codimension at most `finrank R Q`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Module

variable {R : Type*} [Field R] {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]

/-- **The common kernel of a linear map into a dual space has codimension at most
`finrank R Q`**: for `Ψ : Q →ₗ[R] Module.Dual L V` (`R` a subfield of `L`), the subspace
annihilated by the whole image of `Ψ` misses at most `finrank R Q` dimensions.

The `L`-span of the image has dimension at most `finrank R Q`
(`Submodule.finrank_span_le_finrank`), and the common kernel of a space of functionals has
codimension at most its dimension. -/
theorem finrank_le_finrank_iInf_ker_add_finrank {L : Type*} [Field L] [Algebra R L] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (Ψ : Q →ₗ[R] Module.Dual L V) :
    finrank L V ≤ finrank L ↥(⨅ q, LinearMap.ker (Ψ q)) + finrank R Q := by
  set W := Submodule.span L (LinearMap.range Ψ : Set (Module.Dual L V))
  have hsub : W.dualCoannihilator ≤ ⨅ q, LinearMap.ker (Ψ q) :=
    le_iInf fun q v hv ↦
      (Submodule.mem_dualCoannihilator v).mp hv _ (Submodule.subset_span ⟨q, rfl⟩)
  have hle : finrank L W ≤ finrank R Q :=
    (Submodule.finrank_span_le_finrank (LinearMap.range Ψ) (Module.Finite.iff_fg.mp inferInstance))
      |>.trans (LinearMap.finrank_range_le Ψ)
  lia [Subspace.finrank_add_finrank_dualCoannihilator_eq W, Submodule.finrank_mono hsub]

end Module

end
