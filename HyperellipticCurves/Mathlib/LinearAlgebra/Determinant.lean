/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Determinant

-- Beyond the sibling: `Matrix.det_blockDiagonal'` (the mirror of
-- `Mathlib.LinearAlgebra.Matrix.Block`, which `Mathlib.LinearAlgebra.Determinant` does not import).
import HyperellipticCurves.Mathlib.LinearAlgebra.Matrix.Block

/-!
# The determinant of a componentwise endomorphism of a product of modules

## Main statements

* `LinearMap.det_pi'`: the determinant of a componentwise endomorphism of a finite product of
  finite free modules is the product of the determinants; the dependent version of
  `LinearMap.det_pi`.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`), for the norm on a product of
algebras; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace LinearMap

/-- The determinant of a componentwise endomorphism of a finite product of finite free modules
is the product of the determinants of the components. Dependent version of `LinearMap.det_pi`. -/
theorem det_pi' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : ι → Type*}
    [(i : ι) → AddCommGroup (S i)] [(i : ι) → Module R (S i)]
    [(i : ι) → Module.Free R (S i)] [(i : ι) → Module.Finite R (S i)]
    (f : (i : ι) → S i →ₗ[R] S i) :
    (pi fun i ↦ (f i).comp (proj i)).det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (S i)
  rw [← det_toMatrix (Pi.basis b)]
  have h : toMatrix (Pi.basis b) (Pi.basis b) (pi fun i ↦ (f i).comp (proj i)) =
      Matrix.blockDiagonal' fun i ↦ toMatrix (b i) (b i) (f i) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rcases eq_or_ne i₁ j₁ with rfl | hne
    · simp [toMatrix_apply']
    · simp [toMatrix_apply', Matrix.blockDiagonal'_apply_ne _ _ _ hne, Pi.single_eq_of_ne hne]
  rw [h, Matrix.det_blockDiagonal']
  simp [det_toMatrix]

end LinearMap
