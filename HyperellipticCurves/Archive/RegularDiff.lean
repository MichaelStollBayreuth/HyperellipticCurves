/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Disks.CurvePoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Polynomial.DegreeLT

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Regular differentials (blueprint `def:regdiff`)

This file contains the basis half of clause (c) of `thm:omega-prime-global`, on which the main
theorems do not depend: the annihilator argument spends only the trace-form nonvanishing
(`ChabautyColeman.sum_smul_tracePoly_ne_zero`) and the degree bound, never the span/finrank
statement about the space of regular differentials.

The `g`-dimensional space of regular differentials of the odd-degree hyperelliptic curve
`y² = f(x)`: a differential `h(x)·dx/y` with `deg h ≤ g - 1` is represented by its
numerator polynomial `h`, so the space is `ChabautyColeman.RegularDiff K f :=
Polynomial.degreeLT K (genus f)`, a `K`-submodule of `K[X]`. This matches how the rest of
the development handles differentials (the disk expansions and order computations of the
`Disks` folder all take the numerator `h` with `deg h ≤ g - 1` as input).

The `ℤ_p`-lattice of Definition `def:regdiff` (integral numerators) enters only with the
normalization of the pairing `λ` (blueprint `def:lambda1`) and is introduced there.

**Status.** `RegularDiff` is the blueprint anchor for `def:regdiff`; the counting chapter
states regularity directly via degree bounds on the numerator (`deg h₀ < deg u_τ` in
`HyperellipticCurves.Count.Main`), so the submodule itself is not consumed by the assembled proof.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable (K : Type*) [Field K] {R : Type*} [Semiring R] (f : R[X])

/-- The space of **regular differentials** `h(x)·dx/y`, `deg h ≤ g - 1`, of the
odd-degree hyperelliptic curve `y² = f(x)`, represented by the numerator polynomial `h`:
the `K`-submodule `Polynomial.degreeLT K (genus f)` of `K[X]` (blueprint `def:regdiff`).
It is `g`-dimensional (`ChabautyColeman.finrank_regularDiff`). -/
noncomputable def RegularDiff : Submodule K K[X] :=
  Polynomial.degreeLT K (genus f)

theorem mem_regularDiff_iff {h : K[X]} :
    h ∈ RegularDiff K f ↔ h.degree < genus f := by
  rw [RegularDiff, Polynomial.mem_degreeLT]

theorem finrank_regularDiff : Module.finrank K (RegularDiff K f) = genus f := by
  rw [RegularDiff, (Polynomial.degreeLTEquiv K (genus f)).finrank_eq]
  exact Module.finrank_fin_fun K

variable {K f}

/-- A family of `g` numerator polynomials of degree `< g` whose coefficient matrix has
unit determinant is linearly independent in `ChabautyColeman.RegularDiff`. -/
theorem linearIndependent_regularDiff (P : Fin (genus f) → K[X])
    (hdeg : ∀ i, (P i).degree < genus f)
    (hdet : IsUnit (Matrix.of fun i j : Fin (genus f) ↦ (P i).coeff j).det) :
    LinearIndependent K
      fun i ↦ (⟨P i, (mem_regularDiff_iff K f).mpr (hdeg i)⟩ : RegularDiff K f) := by
  have hrows : LinearIndependent K (Matrix.of fun i j : Fin (genus f) ↦ (P i).coeff j).row :=
    Matrix.linearIndependent_row_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  have hcomp : ⇑(Polynomial.degreeLTEquiv K (genus f))
      ∘ (fun i ↦ (⟨P i, (mem_regularDiff_iff K f).mpr (hdeg i)⟩ : RegularDiff K f))
      = (Matrix.of fun i j : Fin (genus f) ↦ (P i).coeff j).row := rfl
  exact LinearIndependent.of_comp (Polynomial.degreeLTEquiv K (genus f)).toLinearMap
    (hcomp ▸ hrows)

/-- **The basis of regular differentials from a unit coordinate determinant** (blueprint
`thm:omega-prime-global` clause (c), basis half): `g` numerators of degree `< g` — e.g. the
numerators of the `ω'_i` produced by `ChabautyColeman.omegaPrime_regular` — whose
coefficient matrix has unit determinant (the good-position Jacobian condition) form a basis of
the space of regular differentials. -/
noncomputable def regularDiffBasis (hg : 0 < genus f) (P : Fin (genus f) → K[X])
    (hdeg : ∀ i, (P i).degree < genus f)
    (hdet : IsUnit (Matrix.of fun i j : Fin (genus f) ↦ (P i).coeff j).det) :
    Module.Basis (Fin (genus f)) K (RegularDiff K f) :=
  have : Nonempty (Fin (genus f)) := Fin.pos_iff_nonempty.mp hg
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_regularDiff P hdeg hdet)
    (by rw [finrank_regularDiff, Fintype.card_fin])

/-- **A nonzero coordinate vector gives a nonzero differential**: under the hypotheses of
`ChabautyColeman.regularDiffBasis` the numerators `P i` are linearly independent, so the
differential with coordinates `cs` in that basis vanishes only for `cs = 0`. This is what
turns a nonzero annihilating *coordinate vector* into a nonzero annihilating differential. -/
theorem sum_smul_ne_zero_of_isUnit_det (P : Fin (genus f) → K[X])
    (hdeg : ∀ i, (P i).degree < genus f)
    (hdet : IsUnit (Matrix.of fun i j : Fin (genus f) ↦ (P i).coeff j).det)
    {cs : Fin (genus f) → K} (hcs : cs ≠ 0) :
    ∑ i, cs i • P i ≠ 0 := fun h ↦
  hcs <| funext fun i ↦ Fintype.linearIndependent_iff.mp
    (linearIndependent_regularDiff P hdeg hdet) cs (Subtype.ext (by simpa using h)) i

@[simp]
theorem regularDiffBasis_apply (hg : 0 < genus f) (P : Fin (genus f) → K[X])
    (hdeg : ∀ i, (P i).degree < genus f)
    (hdet : IsUnit (Matrix.of fun i j : Fin (genus f) ↦ (P i).coeff j).det)
    (i : Fin (genus f)) :
    regularDiffBasis hg P hdeg hdet i
      = (⟨P i, (mem_regularDiff_iff K f).mpr (hdeg i)⟩ : RegularDiff K f) := by
  have : Nonempty (Fin (genus f)) := Fin.pos_iff_nonempty.mp hg
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_regularDiff P hdeg hdet) (by rw [finrank_regularDiff, Fintype.card_fin])) i

end ChabautyColeman

end
