/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Norm.Defs

-- Beyond the sibling: `LinearMap.det_pi'`.
import HyperellipticCurves.Mathlib.LinearAlgebra.Determinant

/-!
# The norm on a product of algebras

## Main statements

* `Algebra.norm_prod`: the norm on `A × B` is the product of the norms of the components.
* `Algebra.norm_pi`: the norm on a finite product of algebras is the product of the norms of the
  components.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`), for the norm on `K[X] ⧸ (f)`
as the product of the norms on its field factors; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Algebra

theorem norm_prod {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (x : A × B) : norm R x = norm R x.1 * norm R x.2 := by
  have h : lmul R (A × B) x = (lmul R A x.1).prodMap (lmul R B x.2) := by
    ext <;> simp
  rw [norm_apply, norm_apply, norm_apply, h, LinearMap.det_prodMap]

theorem norm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : ι → Type*}
    [(i : ι) → CommRing (S i)] [(i : ι) → Algebra R (S i)]
    [(i : ι) → Module.Free R (S i)] [(i : ι) → Module.Finite R (S i)] (g : (i : ι) → S i) :
    norm R g = ∏ i, norm R (g i) := by
  have h : lmul R ((i : ι) → S i) g =
      LinearMap.pi fun i ↦ (lmul R (S i) (g i)).comp (LinearMap.proj i) := by
    ext x j
    simp
  rw [norm_apply, h, LinearMap.det_pi']
  simp_rw [← norm_apply]

end Algebra
