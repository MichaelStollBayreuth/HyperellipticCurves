/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: the normalization of `K[X]` (in the statement of
-- `Polynomial.Factors.mem_normalizedFactors_iff`), `Squarefree`, and for the proofs the
-- irreducible elements of a principal ideal domain.
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

import HyperellipticCurves.Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The monic irreducible factors of a polynomial over a field

## Main definitions

* `Polynomial.Factors f`: the distinct monic irreducible factors of `f : K[X]`, as an index type.
* `Polynomial.Factors.ofRoot`, `Polynomial.Factors.equivOfRoots`: the factor `X - C a` of a root
  `a`, and the factors of a polynomial with distinct roots `α i`, at least `natDegree f` many.

## Main statements

* `Polynomial.Factors.mem_normalizedFactors_iff`: for `f ≠ 0`, the elements of
  `normalizedFactors f` are exactly the monic irreducible factors of `f`.
* `Polynomial.Factors.finite`: `f.Factors` is finite for `f ≠ 0`.
* `Polynomial.Factors.isCoprime`: distinct factors are coprime.
* `Polynomial.Factors.associated_prod`: a squarefree `f` is associated to the product of its
  monic irreducible factors.
* `Polynomial.Factors.span_eq_iInf_span`: for squarefree `f`, the ideal `(f)` is the
  intersection of the ideals `(p)` of its monic irreducible factors.
* `Polynomial.Factors.exists_prod_eq`, `Polynomial.Factors.prod_injective`: the monic divisors of
  a squarefree `f` are the products over the subsets of `f.Factors`, without repetition.
* `Polynomial.Factors.exists_eval₂_eq_zero`: a root of `f` is a root of one of its monic
  irreducible factors.
* `Polynomial.Factors.card_eq_of_injective`: a polynomial with distinct roots `α i`, at least
  `natDegree f` many, has as many monic irreducible factors.
* `Polynomial.Factors.equivOfProd`, `Polynomial.Factors.card_eq_of_associated_prod`: the monic
  irreducible factors of a polynomial associated to a product of distinct monic irreducible
  polynomials `q i` are in bijection with the indices.

## Implementation notes

`Polynomial.Factors f` is the subtype of `K[X]` cut out by a property, not a type built from
`normalizedFactors f`, so that its type does not depend on a `DecidableEq K` instance; it is
infinite for `f = 0`, so finiteness is a lemma with the hypothesis `f ≠ 0`, not an instance.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`), for counting the points of
order `2` on the Jacobian of a hyperelliptic curve; upstreaming candidates for Mathlib.
-/

@[expose] public section

open UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

Note that this is *not* defined via `normalizedFactors` (which would require `DecidableEq K`);
membership in `normalizedFactors f` is characterized by
`Polynomial.Factors.mem_normalizedFactors_iff`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p.Monic ∧ Irreducible p ∧ p ∣ f}

namespace Factors

theorem monic (p : f.Factors) : (p : K[X]).Monic := p.2.1

theorem irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.2.1

theorem dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2

theorem ne_zero (p : f.Factors) : (p : K[X]) ≠ 0 := p.irreducible.ne_zero

theorem prime (p : f.Factors) : Prime (p : K[X]) := p.irreducible.prime

/-- Membership in `normalizedFactors` (with its normalization from `DecidableEq K`) is
equivalent to being a monic irreducible factor: `Polynomial.mem_normalizedFactors_iff` with the
conditions in the order of the predicate defining `Polynomial.Factors`. -/
theorem mem_normalizedFactors_iff [DecidableEq K] (hf : f ≠ 0) {p : K[X]} :
    p ∈ normalizedFactors f ↔ p.Monic ∧ Irreducible p ∧ p ∣ f :=
  (Polynomial.mem_normalizedFactors_iff hf).trans and_left_comm

theorem finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact .of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (mem_normalizedFactors_iff hf).mpr hp).injective

theorem eq_of_dvd {p q : f.Factors} (h : (p : K[X]) ∣ q) : p = q :=
  Subtype.ext <| eq_of_monic_of_associated p.monic q.monic <|
    p.irreducible.associated_of_dvd q.irreducible h

theorem isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  p.irreducible.coprime_iff_not_dvd.mpr fun h ↦ hne (eq_of_dvd h)

/-- A squarefree polynomial is associated to the product of its monic irreducible factors. -/
theorem associated_prod [Fintype f.Factors] (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  have hf := hsq.ne_zero
  rw [← Finset.prod_subtype (normalizedFactors f).toFinset
      (fun p ↦ by rw [Multiset.mem_toFinset, mem_normalizedFactors_iff hf]) fun p ↦ p,
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
    Multiset.map_id']
  exact prod_normalizedFactors hf

theorem dvd_prod_iff (q : f.Factors) (s : Finset f.Factors) :
    (q : K[X]) ∣ ∏ p ∈ s, (p : K[X]) ↔ q ∈ s := by
  refine ⟨fun h ↦ ?_, fun h ↦ Finset.dvd_prod_of_mem _ h⟩
  obtain ⟨p, hp, hqp⟩ := q.prime.exists_mem_finset_dvd h
  rwa [eq_of_dvd hqp]

theorem prod_injective : Function.Injective fun s : Finset f.Factors ↦ ∏ p ∈ s, (p : K[X]) :=
  fun s t h ↦ Finset.ext fun q ↦ by
    simp only at h
    rw [← dvd_prod_iff, h, dvd_prod_iff]

theorem monic_prod (s : Finset f.Factors) : (∏ p ∈ s, (p : K[X])).Monic :=
  monic_prod_of_monic _ _ fun p _ ↦ p.monic

theorem prod_dvd (s : Finset f.Factors) : ∏ p ∈ s, (p : K[X]) ∣ f :=
  Finset.prod_dvd_of_coprime (fun _ _ _ _ hpq ↦ isCoprime hpq) fun p _ ↦ p.dvd

/-- Every monic divisor of a squarefree `f` is the product of a set of monic irreducible factors
of `f`; with `Polynomial.Factors.prod_injective`, the monic divisors of `f` correspond to the
subsets of `f.Factors`. -/
theorem exists_prod_eq (hsq : Squarefree f) {h : K[X]} (hm : h.Monic) (hh : h ∣ f) :
    ∃ s : Finset f.Factors, ∏ p ∈ s, (p : K[X]) = h := by
  classical
  have := finite hsq.ne_zero
  have := Fintype.ofFinite f.Factors
  refine ⟨({p | (p : K[X]) ∣ h} : Finset f.Factors), eq_of_monic_of_associated (monic_prod _) hm
    (associated_of_dvd_dvd (Finset.prod_dvd_of_coprime (fun _ _ _ _ hpq ↦ isCoprime hpq)
      fun p hp ↦ (Finset.mem_filter.mp hp).2) ?_)⟩
  have hc : IsCoprime h (∏ p : f.Factors with ¬p.1 ∣ h, p.1) := IsCoprime.prod_right fun p hp ↦
    (p.irreducible.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hp).2).symm
  refine hc.dvd_of_dvd_mul_right ?_
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact hh.trans (associated_prod hsq).symm.dvd

theorem associated_prod_mul_prod_compl [Fintype f.Factors] [DecidableEq f.Factors]
    (hsq : Squarefree f) (s : Finset f.Factors) :
    Associated ((∏ p ∈ s, (p : K[X])) * ∏ p ∈ sᶜ, (p : K[X])) f :=
  Finset.prod_mul_prod_compl s (fun p ↦ (p : K[X])) ▸ associated_prod hsq

theorem natDegree_prod_add_natDegree_prod_compl [Fintype f.Factors] [DecidableEq f.Factors]
    (hsq : Squarefree f) (s : Finset f.Factors) :
    (∏ p ∈ s, (p : K[X])).natDegree + (∏ p ∈ sᶜ, (p : K[X])).natDegree = f.natDegree := by
  rw [← natDegree_mul (monic_prod s).ne_zero (monic_prod sᶜ).ne_zero]
  exact natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (associated_prod_mul_prod_compl hsq s))

theorem isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

theorem span_eq_iInf_span (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have := finite hsq.ne_zero
  have := Fintype.ofFinite f.Factors
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hsq)).symm

/-- A root `α` in a domain `E` of a nonzero polynomial `f` over a field `K`, for a ring
homomorphism `φ : K →+* E`, is a root of one of the monic irreducible factors of `f`: its minimal
polynomial. -/
theorem exists_eval₂_eq_zero {E : Type*} [CommRing E] [IsDomain E] {φ : K →+* E} (hf : f ≠ 0)
    {α : E} (h : f.eval₂ φ α = 0) : ∃ q : f.Factors, (q : K[X]).eval₂ φ α = 0 := by
  let : Algebra K E := φ.toAlgebra
  have hα : IsIntegral K α := IsAlgebraic.isIntegral ⟨f, hf, h⟩
  exact ⟨⟨minpoly K α, minpoly.monic hα, minpoly.irreducible hα, minpoly.dvd K α h⟩,
    minpoly.aeval K α⟩

/-- The monic irreducible factor `X - C a` of `f`, for a root `a` of `f`. -/
noncomputable def ofRoot {a : K} (ha : f.IsRoot a) : f.Factors :=
  ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, dvd_iff_isRoot.mpr ha⟩

@[simp]
theorem coe_ofRoot {a : K} (ha : f.IsRoot a) : (ofRoot ha : K[X]) = X - C a :=
  rfl

variable {ι : Type*} [Fintype ι] {α : ι → K}

/-- For a nonzero `f` with distinct roots `α i`, at least `natDegree f` many, the monic
irreducible factors of `f` are the `X - C (α i)`. -/
noncomputable def equivOfRoots (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) : ι ≃ f.Factors :=
  .ofBijective (fun i ↦ ofRoot (hroot i))
    ⟨fun i j h ↦ hinj (by simpa using congr(Subtype.val $h)), fun p ↦ by
      have hp : (p : K[X]) ∣ ∏ i, (X - C (α i)) := by
        rw [← dvd_C_mul (leadingCoeff_ne_zero.mpr hf),
          ← eq_C_leadingCoeff_mul_prod_X_sub_C_of_injective hinj hroot hcard]
        exact p.dvd
      obtain ⟨i, -, hi⟩ := p.prime.exists_mem_finset_dvd hp
      exact ⟨i, (eq_of_dvd (q := ofRoot (hroot i)) hi).symm⟩⟩

@[simp]
theorem equivOfRoots_apply (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) (i : ι) :
    equivOfRoots hf hinj hroot hcard i = ofRoot (hroot i) :=
  rfl

/-- A nonzero `f` with distinct roots `α i`, at least `natDegree f` many, has as many monic
irreducible factors as there are roots. -/
theorem card_eq_of_injective (hf : f ≠ 0) (hinj : Function.Injective α)
    (hroot : ∀ i, f.IsRoot (α i)) (hcard : f.natDegree ≤ Fintype.card ι) :
    Nat.card f.Factors = Fintype.card ι :=
  (Nat.card_congr (equivOfRoots hf hinj hroot hcard).symm).trans Nat.card_eq_fintype_card

variable {q : ι → K[X]}

/-- For `f` associated to the product of distinct monic irreducible polynomials `q i`, the monic
irreducible factors of `f` are the `q i`. -/
noncomputable def equivOfProd (hmonic : ∀ i, (q i).Monic) (hirr : ∀ i, Irreducible (q i))
    (hinj : Function.Injective q) (hf : Associated (∏ i, q i) f) : ι ≃ f.Factors :=
  .ofBijective
    (fun i ↦ ⟨q i, hmonic i, hirr i, (Finset.dvd_prod_of_mem q (Finset.mem_univ i)).trans hf.dvd⟩)
    ⟨fun _ _ h ↦ hinj congr(Subtype.val $h), fun p ↦
      let ⟨i, _, hi⟩ := p.prime.exists_mem_finset_dvd (p.dvd.trans hf.symm.dvd)
      ⟨i, Eq.symm (eq_of_dvd hi)⟩⟩

@[simp]
theorem coe_equivOfProd_apply (hmonic : ∀ i, (q i).Monic) (hirr : ∀ i, Irreducible (q i))
    (hinj : Function.Injective q) (hf : Associated (∏ i, q i) f) (i : ι) :
    (equivOfProd hmonic hirr hinj hf i : K[X]) = q i :=
  rfl

/-- A polynomial associated to the product of distinct monic irreducible polynomials `q i` has as
many monic irreducible factors as there are `q i`. -/
theorem card_eq_of_associated_prod (hmonic : ∀ i, (q i).Monic) (hirr : ∀ i, Irreducible (q i))
    (hinj : Function.Injective q) (hf : Associated (∏ i, q i) f) :
    Nat.card f.Factors = Fintype.card ι :=
  (Nat.card_congr (equivOfProd hmonic hirr hinj hf).symm).trans Nat.card_eq_fintype_card

end Factors

end Polynomial
