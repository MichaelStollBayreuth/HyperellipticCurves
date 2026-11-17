/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Defs

/-!
# Components of finite sums in a quadratic algebra

## Main statements

* `QuadraticAlgebra.re_sum`, `QuadraticAlgebra.im_sum`: the real and imaginary parts of a finite
  sum are the sums of the parts.

They serve the place-by-place valuation bounds (`HyperellipticCurves.Archive.OmegaRegular`).

Auxiliary material for the Archive of the formalization of the Chabauty–Coleman bound for
hyperelliptic curves (the main theorems do not depend on it); upstreaming candidates for
Mathlib.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The real part of a finite sum in a quadratic algebra. -/
theorem re_sum {R : Type*} [CommRing R] {a b : R} {ι : Type*}
    (s : Finset ι) (g : ι → QuadraticAlgebra R a b) :
    (∑ j ∈ s, g j).re = ∑ j ∈ s, (g j).re :=
  map_sum (AddMonoidHom.mk' QuadraticAlgebra.re fun _ _ ↦ rfl) g s

/-- The imaginary part of a finite sum in a quadratic algebra. -/
theorem im_sum {R : Type*} [CommRing R] {a b : R} {ι : Type*}
    (s : Finset ι) (g : ι → QuadraticAlgebra R a b) :
    (∑ j ∈ s, g j).im = ∑ j ∈ s, (g j).im :=
  map_sum (AddMonoidHom.mk' QuadraticAlgebra.im fun _ _ ↦ rfl) g s

end QuadraticAlgebra

end
