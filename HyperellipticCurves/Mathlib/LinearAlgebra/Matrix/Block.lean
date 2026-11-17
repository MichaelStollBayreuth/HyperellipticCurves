/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The determinant of a block diagonal matrix with blocks of different sizes

## Main statements

* `Matrix.det_blockDiagonal'`: the determinant of `Matrix.blockDiagonal' M` is the product of the
  determinants of the blocks; the dependent version of `Matrix.det_blockDiagonal`.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`), for the norm on a product of
algebras; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace Matrix

/-- The determinant of a block diagonal matrix with (possibly) non-uniform block sizes is the
product of the determinants of the blocks: the matrix is block triangular for `Sigma.fst`. -/
theorem det_blockDiagonal' {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → Type*}
    [(i : ι) → Fintype (η i)] [(i : ι) → DecidableEq (η i)] {R : Type*} [CommRing R]
    (M : (i : ι) → Matrix (η i) (η i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  let : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  have hbt : (blockDiagonal' M).BlockTriangular Sigma.fst :=
    fun x y h ↦ blockDiagonal'_apply_ne _ _ _ h.ne'
  rw [hbt.det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← det_reindex_self (Equiv.sigmaSubtype k)]
  congr 1
  ext j j'
  exact blockDiagonal'_apply_eq M k j j'

end Matrix
