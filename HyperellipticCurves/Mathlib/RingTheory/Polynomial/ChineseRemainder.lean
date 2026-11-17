/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- No Mathlib sibling (a new file); `Mathlib.FieldTheory.Perfect` brings `AdjoinRoot` and the
-- Chinese remainder theorem along.
public import HyperellipticCurves.Mathlib.GroupTheory.QuotientGroup.UnitsModPow
public import HyperellipticCurves.Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.FieldTheory.Perfect

import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Lagrange

/-!
# `K[X] ⧸ (f)` as a product of fields

For a squarefree polynomial `f` over a field `K`, the Chinese remainder theorem makes
`AdjoinRoot f` the product of the fields `AdjoinRoot p`, where `p` runs over the monic irreducible
factors `Polynomial.Factors f` of `f`. This is what lets one talk about the primes, and hence the
Selmer groups, of `AdjoinRoot f`: they are those of the factors.

## Main definitions

* `AdjoinRoot.equivPiFactors`: the `K`-algebra isomorphism
  `AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot p)`.
* `AdjoinRoot.projFactor`: its component at the factor `p`, the reduction `K[X] ⧸ (f) → K[X] ⧸ (p)`.
* `AdjoinRoot.modPowEquivPiFactors`: the induced isomorphism of the groups of units modulo `n`-th
  powers, `Units.ModPow (AdjoinRoot f) n ≃* ((p : f.Factors) → Units.ModPow (AdjoinRoot p) n)`.
* `AdjoinRoot.equivPiOfRoots`, `AdjoinRoot.modPowEquivPiOfRoots`: for distinct roots `α i` of `f`,
  at least `natDegree f` many, the root coordinates `AdjoinRoot f ≃ₐ[K] (ι → K)` (evaluation at
  the `α i`) and `Units.ModPow (AdjoinRoot f) n ≃* (ι → Units.ModPow K n)`.

## Main statements

* `AdjoinRoot.lift_projFactor`, `AdjoinRoot.map_lift_modPowEquivPiFactors`: evaluation at a root of
  a factor `p` of `f` factors through the projection `AdjoinRoot.projFactor` onto the field factor
  `K[X] ⧸ (p)`, also on `n`-th power classes.
* `AdjoinRoot.projFactor_of`, `AdjoinRoot.projFactor_root`: `AdjoinRoot.projFactor` maps the
  constants and the root of `K[X] ⧸ (f)` to those of `K[X] ⧸ (p)`.
* `AdjoinRoot.modPowEquivPiFactors_mk`: on the class of a unit, `AdjoinRoot.modPowEquivPiFactors`
  is componentwise `AdjoinRoot.projFactor`; `AdjoinRoot.modPowEquivPiFactors_unit` for the unit of
  an element.
* `AdjoinRoot.modPow_mk_eq_one_iff_forall_factors`: the class of a unit is trivial exactly when
  all its components are.
* `AdjoinRoot.map_lift_modPowEquivPiFactors_symm_mulSingle`,
  `AdjoinRoot.map_lift_modPowEquivPiFactors_symm_mulSingle_of_ne`: evaluation at a root of the
  factor `p` of the class with component `c` at `p` and trivial components elsewhere: the image of
  `c`, resp. `1` at a root of another factor.
* `AdjoinRoot.modPowEquivPiFactors_ofRoot`: the component at the factor `X - C a` is evaluation
  at `a`.
* `AdjoinRoot.modPowEquivPiOfRoots_map`: the root coordinates commute with base change.

## Implementation notes

The factors carry the instances `Polynomial.Factors.instFactIrreducible` (so that each
`AdjoinRoot p` is a field), `AdjoinRoot.instModuleFiniteFactors` and, for a perfect field `K`,
`AdjoinRoot.instIsSeparableFactors` and `AdjoinRoot.instPerfectFieldFactors`.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`, section `EtaleDecomposition`),
for the Selmer groups of `K[X] ⧸ (f)`; upstreaming candidates for Mathlib.
-/

@[expose] public section

open Polynomial

namespace Polynomial.Factors

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

end Polynomial.Factors

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instModuleFiniteFactors (p : f.Factors) : Module.Finite K (AdjoinRoot (p : K[X])) :=
  p.monic.finite_adjoinRoot

/-- Over a perfect field, the field factors of `K[X] ⧸ (f)` are separable. This is the instance
`Algebra.IsAlgebraic.isSeparable_of_perfectField`, restated for the factors because instance
search does not find that one for the family `(p : f.Factors) → Algebra.IsSeparable K _`. -/
instance instIsSeparableFactors [PerfectField K] (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- Over a perfect field, the field factors of `K[X] ⧸ (f)` are perfect: Mathlib's
`Algebra.IsAlgebraic.perfectField`, which instance search cannot apply (it does not know `K`). -/
instance instPerfectFieldFactors [PerfectField K] (p : f.Factors) :
    PerfectField (AdjoinRoot (p : K[X])) :=
  Algebra.IsAlgebraic.perfectField K

/-- **Chinese remainder theorem** for `AdjoinRoot`: for squarefree `f`, `K[X] ⧸ (f)` is the
product of the fields `K[X] ⧸ (p)` over the monic irreducible factors `p` of `f`. -/
noncomputable def equivPiFactors (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  have : Finite f.Factors := Factors.finite hsq.ne_zero
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl

@[simp]
theorem equivPiFactors_mk (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    equivPiFactors hsq (mk f q) p = mk (p : K[X]) q :=
  rfl

/-- The reduction `K[X] ⧸ (f) → K[X] ⧸ (p)` onto the field factor of the monic irreducible
factor `p` of `f`, the component of `AdjoinRoot.equivPiFactors`. -/
noncomputable def projFactor (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →+* AdjoinRoot (p : K[X]) :=
  (Pi.evalRingHom _ p).comp (equivPiFactors hsq).toRingEquiv.toRingHom

@[simp]
theorem projFactor_mk (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hsq p (mk f q) = mk (p : K[X]) q :=
  rfl

@[simp]
theorem projFactor_of (hsq : Squarefree f) (p : f.Factors) (x : K) :
    projFactor hsq p (of f x) = of (p : K[X]) x :=
  rfl

@[simp]
theorem projFactor_root (hsq : Squarefree f) (p : f.Factors) :
    projFactor hsq p (root f) = root (p : K[X]) :=
  rfl

/-- The `n`-th power classes of units of `K[X] ⧸ (f)` are the product of those of its field
factors. -/
noncomputable def modPowEquivPiFactors (hsq : Squarefree f) (n : ℕ) :
    Units.ModPow (AdjoinRoot f) n ≃*
      ((p : f.Factors) → Units.ModPow (AdjoinRoot (p : K[X])) n) :=
  (Units.ModPow.congr (equivPiFactors hsq).toMulEquiv n).trans <|
    Units.ModPow.piEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n

@[simp]
theorem modPowEquivPiFactors_mk (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) (p : f.Factors) :
    modPowEquivPiFactors hsq n u p =
      (Units.map (projFactor hsq p).toMonoidHom u : Units.ModPow (AdjoinRoot (p : K[X])) n) :=
  rfl

theorem modPowEquivPiFactors_unit (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hsq n ha.unit p =
      ((ha.map (projFactor hsq p)).unit : Units.ModPow (AdjoinRoot (p : K[X])) n) :=
  (modPowEquivPiFactors_mk ..).trans (congrArg _ (Units.ext rfl))

theorem modPow_mk_eq_one_iff_forall_factors (hsq : Squarefree f) (n : ℕ) (u : (AdjoinRoot f)ˣ) :
    (u : Units.ModPow (AdjoinRoot f) n) = 1 ↔ ∀ p : f.Factors,
      (Units.map (projFactor hsq p).toMonoidHom u : Units.ModPow (AdjoinRoot (p : K[X])) n) =
        1 := by
  rw [← (modPowEquivPiFactors hsq n).map_eq_one_iff, funext_iff]
  simp

end AdjoinRoot

namespace AdjoinRoot

section Roots

variable {K : Type*} [Field K] {f : K[X]} {ι : Type*} {α : ι → K}

/-- Evaluation at distinct roots `α i` of `f` is surjective on `K[X] ⧸ (f)`, by Lagrange
interpolation. -/
theorem pi_liftAlgHom_surjective [Finite ι] (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) :
    Function.Surjective
      (AlgHom.pi fun i ↦ liftAlgHom f (Algebra.ofId K K) (α i) (by simpa using hroot i)) := by
  classical
  have := Fintype.ofFinite ι
  exact fun r ↦ ⟨mk f (Lagrange.interpolate Finset.univ α r), funext fun i ↦
    Lagrange.eval_interpolate_at_node r hinj.injOn (Finset.mem_univ i)⟩

variable [Fintype ι]

/-- **Root coordinates**: for distinct roots `α i` of `f ≠ 0`, at least `natDegree f` many,
`K[X] ⧸ (f)` is the product of copies of `K`, by evaluation at the `α i`. -/
noncomputable def equivPiOfRoots (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) :
    AdjoinRoot f ≃ₐ[K] (ι → K) :=
  .ofBijective (.pi fun i ↦ liftAlgHom f (Algebra.ofId K K) (α i) (by simpa using hroot i)) <| by
    have := (powerBasis hf).finite
    rw [← AlgHom.coe_toLinearMap]
    refine OrzechProperty.bijective_of_surjective_of_finrank_le _
      (by simpa using pi_liftAlgHom_surjective hinj hroot) ?_
    rwa [(powerBasis hf).finrank, powerBasis_dim, Module.finrank_fintype_fun_eq_card]

@[simp]
theorem equivPiOfRoots_apply (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) (x : AdjoinRoot f)
    (i : ι) :
    equivPiOfRoots hf hinj hroot hcard x i =
      liftAlgHom f (Algebra.ofId K K) (α i) (by simpa using hroot i) x :=
  rfl

/-- **Root coordinates** of the `n`-th power classes: for distinct roots `α i` of `f ≠ 0`, at
least `natDegree f` many, the classes of units of `K[X] ⧸ (f)` modulo `n`-th powers are tuples of
classes of `K`, by evaluation at the `α i`. -/
noncomputable def modPowEquivPiOfRoots (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) (n : ℕ) :
    Units.ModPow (AdjoinRoot f) n ≃* (ι → Units.ModPow K n) :=
  (Units.ModPow.congr (equivPiOfRoots hf hinj hroot hcard).toMulEquiv n).trans <|
    Units.ModPow.piEquiv (fun _ : ι ↦ K) n

@[simp]
theorem modPowEquivPiOfRoots_apply (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) (n : ℕ)
    (x : Units.ModPow (AdjoinRoot f) n) (i : ι) :
    modPowEquivPiOfRoots hf hinj hroot hcard n x i =
      Units.ModPow.map (liftAlgHom f (Algebra.ofId K K) (α i) (by simpa using hroot i)) n x := by
  induction x using QuotientGroup.induction_on with | H u => rfl

/-- The component of `K[X] ⧸ (f)` at the linear factor `X - C a` of `f` is evaluation at `a`. -/
theorem projFactor_ofRoot (hsq : Squarefree f) {a : K} (ha : f.IsRoot a) (x : AdjoinRoot f) :
    projFactor hsq (Factors.ofRoot ha) x =
      algebraMap K _ (liftAlgHom f (Algebra.ofId K K) a (by simpa using ha) x) := by
  induction x using AdjoinRoot.induction_on with | ih g => ?_
  rw [projFactor_mk, liftAlgHom_mk, algebraMap_eq, ← mk_C, mk_eq_mk]
  exact X_sub_C_dvd_sub_C_eval

/-- The component of an `n`-th power class of `K[X] ⧸ (f)` at the linear factor `X - C a` of `f`
is the image of its evaluation at `a`. -/
theorem modPowEquivPiFactors_ofRoot (hsq : Squarefree f) {a : K} (ha : f.IsRoot a) {n : ℕ}
    (x : Units.ModPow (AdjoinRoot f) n) :
    modPowEquivPiFactors hsq n x (Factors.ofRoot ha) =
      Units.ModPow.map (algebraMap K (AdjoinRoot (Factors.ofRoot ha : K[X])) : K →* _) n
        (Units.ModPow.map
          (liftAlgHom f (Algebra.ofId K K) a (by simpa using ha) : AdjoinRoot f →* K) n x) := by
  induction x using QuotientGroup.induction_on with | H u => ?_
  simp only [modPowEquivPiFactors_mk, Units.ModPow.map_mk]
  congr 1
  ext
  exact projFactor_ofRoot hsq ha _

variable {A : Type*} [CommRing A] {φ : K →+* A} {ρ : A}

/-- Evaluation of `K[X] ⧸ (f)` at a root `ρ` of a factor `p` of `f` factors through the
projection onto the field factor `K[X] ⧸ (p)`. -/
theorem lift_projFactor (hsq : Squarefree f) (p : f.Factors) (hρ : (p : K[X]).eval₂ φ ρ = 0)
    (x : AdjoinRoot f) :
    lift φ ρ hρ (projFactor hsq p x) =
      lift φ ρ (eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ p.dvd hρ) x := by
  induction x using AdjoinRoot.induction_on with | ih q => simp [lift_mk]

/-- The image of an `n`-th power class of `K[X] ⧸ (f)` under evaluation at a root `ρ` of a factor
`p` of `f` is the image of its component at `p`. -/
theorem map_lift_modPowEquivPiFactors (hsq : Squarefree f) (p : f.Factors)
    (hρ : (p : K[X]).eval₂ φ ρ = 0) {n : ℕ} (x : Units.ModPow (AdjoinRoot f) n) :
    Units.ModPow.map (lift φ ρ hρ : AdjoinRoot (p : K[X]) →* A) n
        (modPowEquivPiFactors hsq n x p) =
      Units.ModPow.map (lift φ ρ (eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ p.dvd hρ) :
        AdjoinRoot f →* A) n x := by
  induction x using QuotientGroup.induction_on with | H u => ?_
  simp only [modPowEquivPiFactors_mk, Units.ModPow.map_mk]
  congr 1
  ext
  exact lift_projFactor hsq p hρ _

section Factors

variable [DecidableEq f.Factors]

/-- Evaluation at a root `ρ` of the factor `p` of `f` maps the class with component `c` at `p`
and trivial components elsewhere to the image of `c`. -/
theorem map_lift_modPowEquivPiFactors_symm_mulSingle (hsq : Squarefree f) (p : f.Factors)
    (hρ : (p : K[X]).eval₂ φ ρ = 0) {n : ℕ} (c : Units.ModPow (AdjoinRoot (p : K[X])) n) :
    Units.ModPow.map (lift φ ρ (eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ p.dvd hρ) :
        AdjoinRoot f →* A) n ((modPowEquivPiFactors hsq n).symm (Pi.mulSingle p c)) =
      Units.ModPow.map (lift φ ρ hρ : AdjoinRoot (p : K[X]) →* A) n c := by
  rw [← map_lift_modPowEquivPiFactors hsq p hρ, MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]

/-- Evaluation at a root `ρ` of the factor `q` of `f` kills the classes with trivial component
at `q`. -/
theorem map_lift_modPowEquivPiFactors_symm_mulSingle_of_ne (hsq : Squarefree f)
    {p q : f.Factors} (hpq : q ≠ p) (hρ : (q : K[X]).eval₂ φ ρ = 0) {n : ℕ}
    (c : Units.ModPow (AdjoinRoot (p : K[X])) n) :
    Units.ModPow.map (lift φ ρ (eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ q.dvd hρ) :
        AdjoinRoot f →* A) n ((modPowEquivPiFactors hsq n).symm (Pi.mulSingle p c)) = 1 := by
  rw [← map_lift_modPowEquivPiFactors hsq q hρ, MulEquiv.apply_symm_apply,
    Pi.mulSingle_eq_of_ne hpq, map_one]

end Factors

end Roots

section Map

variable {K K' : Type*} [Field K] [Field K'] {f : K[X]}

variable {ι : Type*} [Fintype ι] {α : ι → K} {β : ι → K'}

/-- **Naturality of root coordinates**: for a field homomorphism `φ : K →+* K'` and roots
`β i = φ (α i)`, the root coordinates of the image of `x` in `K'[X] ⧸ (f)` are the images of
those of `x`. -/
theorem modPowEquivPiOfRoots_map (φ : K →+* K') (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι)
    {hf' : f.map φ ≠ 0} {hinj' : Function.Injective β} {hroot' : ∀ i, (f.map φ).IsRoot (β i)}
    {hcard' : (f.map φ).natDegree ≤ Fintype.card ι} (hβ : ∀ i, φ (α i) = β i) {n : ℕ}
    (x : Units.ModPow (AdjoinRoot f) n) (i : ι) :
    modPowEquivPiOfRoots hf' hinj' hroot' hcard' n
        (Units.ModPow.map (map φ f (f.map φ) dvd_rfl) n x) i =
      Units.ModPow.map (φ : K →* K') n (modPowEquivPiOfRoots hf hinj hroot hcard n x i) := by
  induction x using QuotientGroup.induction_on with | H u => ?_
  simp only [modPowEquivPiOfRoots_apply, Units.ModPow.map_mk]
  congr 1
  ext
  exact liftAlgHom_map φ (hroot i) (hroot' i) (hβ i) _

end Map

end AdjoinRoot
