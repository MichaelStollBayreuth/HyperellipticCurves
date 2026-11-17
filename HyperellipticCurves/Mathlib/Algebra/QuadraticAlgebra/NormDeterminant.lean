/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.Algebra.QuadraticAlgebra.NormDeterminant`: the algebra norm and
-- trace, for the statements.
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs

/-!
# The algebra norm and trace of a quadratic algebra

## Main statements

* `QuadraticAlgebra.algebraNorm_eq_norm`: the norm of `QuadraticAlgebra R a b` agrees with the
  determinant norm `Algebra.norm` of the algebra over `R`.
* `QuadraticAlgebra.algebraTrace_eq`: the trace `Algebra.trace`, computed in the basis `1, ω`:
  `2 * z.re + b * z.im`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R} {S : Type*} [CommSemiring S] [Algebra S R]

section normTrace

/-- The norm of `QuadraticAlgebra R a b` agrees with the field-theoretic
(determinant) norm of the algebra `QuadraticAlgebra R a b` over `R`. -/
theorem algebraNorm_eq_norm (z : QuadraticAlgebra R a b) :
    Algebra.norm R z = z.norm := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  congr 1

/-- The field-theoretic trace of `QuadraticAlgebra R a b` over `R`, computed in the
basis `1, ω`. -/
theorem algebraTrace_eq (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = 2 * z.re + b * z.im := by
  classical
  rw [Algebra.trace_eq_matrix_trace (basis a b), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, basis, Module.Basis.coe_ofEquivFun]
  ring

end normTrace

end QuadraticAlgebra

end
