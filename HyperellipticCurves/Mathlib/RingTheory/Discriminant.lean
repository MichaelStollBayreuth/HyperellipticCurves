/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import HyperellipticCurves.Mathlib.RingTheory.Norm.AdjoinRoot

/-!
# The discriminant of an `AdjoinRoot`

## Main statements

* `AdjoinRoot.discr_powerBasis_eq_discr`: the discriminant of the power basis of `K[X] ⧸ (f)` is
  the discriminant of the monic irreducible polynomial `f`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians; an
upstreaming candidate for Mathlib.
-/

@[expose] public section

open Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

/-- The discriminant of the power basis of `K[X] ⧸ (f)`, for `f` monic irreducible with derivative
of degree `deg f - 1` (automatic in characteristic `0`, `Polynomial.natDegree_derivative`), is the
discriminant of `f`: by `Algebra.discr_powerBasis_eq_norm`, it is `± N(f'(θ))`, and
`AdjoinRoot.norm_mk_eq_resultant` and `Polynomial.resultant_deriv` give
`N(f'(θ)) = Res(f, f') = ± disc f`, with the same sign. -/
theorem discr_powerBasis_eq_discr [Fact (Irreducible f)] [Algebra.IsSeparable K (AdjoinRoot f)]
    (hf : f.Monic) (hd : f.derivative.natDegree = f.natDegree - 1) :
    Algebra.discr K (powerBasis hf.ne_zero).basis = f.discr := by
  have : Module.Finite K (AdjoinRoot f) := hf.finite_adjoinRoot
  rw [Algebra.discr_powerBasis_eq_norm, (powerBasis hf.ne_zero).finrank, powerBasis_dim,
    powerBasis_gen, minpoly_root hf.ne_zero, hf.leadingCoeff, inv_one, map_one, mul_one,
    aeval_eq, norm_mk_eq_resultant hf, hd, resultant_deriv (Fact.out : Irreducible f).degree_pos,
    hf.leadingCoeff, mul_one, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

end AdjoinRoot
