/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.LinearCombination

/-!
# The universal Mumford datum ring

`ChabautyColeman.DatumRing R f m k` is the coordinate ring of Mumford data on the curve
`y² = f(x)`: the quotient of the polynomial ring in the coefficients of a monic `u` of
degree `m`, a `v` of degree `< m` and a cofactor `w` of degree `≤ k` by the coefficients
of the curve relation `v² - f - u·w` — and nothing else. The universal datum
(`ChabautyColeman.datumU`/`datumV`/`datumW`) satisfies the relation
(`ChabautyColeman.datumV_sq_sub`), and every concrete datum over an `R`-algebra receives
a unique coordinate specialization (`ChabautyColeman.datumSpec`, with
`ChabautyColeman.datumSpec_map_datumU` etc.).

This is the base object of the *generic Cantor pipeline*: a claim about the pipeline on universal
data is transported to concrete data through `datumSpec`, and for a family of data — one block of
coordinates per member in `ChabautyColeman.DatumFamRing` — through `ChabautyColeman.datumFamSpec`,
so no irreducibility of the Mumford coordinate ring is ever needed.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-- A polynomial of degree `< n` is the sum of its first `n` coefficient monomials. -/
theorem sum_C_coeff_mul_X_pow {S : Type*} [CommRing S] {n : ℕ} {q : S[X]}
    (hq : q.degree < (n : WithBot ℕ)) :
    ∑ i : Fin n, Polynomial.C (q.coeff i) * Polynomial.X ^ (i : ℕ) = q :=
  (Polynomial.sum_fin (fun i c ↦ Polynomial.C c * Polynomial.X ^ i) (by simp) hq).trans
    q.sum_C_mul_X_pow_eq

/-- Coordinate variables of a universal Mumford datum: the `m` lower coefficients of the
monic `u`, the `m` coefficients of `v` (degree `< m`), and the `k + 1` coefficients of
the cofactor `w` (degree `≤ k`). -/
def MumfordVar (m k : ℕ) : Type := Fin m ⊕ Fin m ⊕ Fin (k + 1)

namespace MumfordVar

variable {m k : ℕ}

/-- The variable for the `i`-th coefficient of `u`. -/
def uVar (i : Fin m) : MumfordVar m k := Sum.inl i

/-- The variable for the `i`-th coefficient of `v`. -/
def vVar (i : Fin m) : MumfordVar m k := Sum.inr (Sum.inl i)

/-- The variable for the `i`-th coefficient of `w`. -/
def wVar (i : Fin (k + 1)) : MumfordVar m k := Sum.inr (Sum.inr i)

/-- Assemble a function on the coordinate variables from its three blocks. Stating it as a
declaration of type `MumfordVar m k → A` (rather than inlining `Sum.elim`) keeps the
applications below well-typed without unfolding `MumfordVar`. -/
def elim {A : Sort*} (fu fv : Fin m → A) (fw : Fin (k + 1) → A) : MumfordVar m k → A :=
  Sum.elim fu (Sum.elim fv fw)

variable {A : Sort*} {fu fv : Fin m → A} {fw : Fin (k + 1) → A}

@[simp] theorem elim_uVar (i : Fin m) : elim fu fv fw (uVar i) = fu i := rfl
@[simp] theorem elim_vVar (i : Fin m) : elim fu fv fw (vVar i) = fv i := rfl
@[simp] theorem elim_wVar (i : Fin (k + 1)) : elim fu fv fw (wVar i) = fw i := rfl

end MumfordVar

variable (R : Type*) [CommRing R] (f : R[X]) (m k : ℕ)

open MumfordVar MvPolynomial

/-- The universal monic `u`-polynomial of degree `m`. -/
noncomputable def univU : Polynomial (MvPolynomial (MumfordVar m k) R) :=
  Polynomial.X ^ m
    + ∑ i : Fin m, Polynomial.C (X (uVar i)) * Polynomial.X ^ (i : ℕ)

/-- The universal `v`-polynomial of degree `< m`. -/
noncomputable def univV : Polynomial (MvPolynomial (MumfordVar m k) R) :=
  ∑ i : Fin m, Polynomial.C (X (vVar i)) * Polynomial.X ^ (i : ℕ)

/-- The universal cofactor polynomial of degree `≤ k`. -/
noncomputable def univW : Polynomial (MvPolynomial (MumfordVar m k) R) :=
  ∑ i : Fin (k + 1), Polynomial.C (X (wVar (m := m) i)) * Polynomial.X ^ (i : ℕ)

variable {R m k}

theorem univV_degree : (univV R m k).degree < (m : WithBot ℕ) :=
  degree_sum_fin_lt _

theorem univW_degree : (univW R m k).degree < ((k : WithBot ℕ) + 1) :=
  mod_cast degree_sum_fin_lt fun i : Fin (k + 1) ↦
    (MvPolynomial.X (wVar (m := m) (k := k) i) : MvPolynomial (MumfordVar m k) R)

variable (R m k) in
/-- The ideal of relations of the universal Mumford datum: the coefficients of
`v² - f - u·w`. -/
noncomputable def datumRelIdeal : Ideal (MvPolynomial (MumfordVar m k) R) :=
  Ideal.span (Set.range fun i : ℕ ↦
    ((univV R m k) ^ 2 - f.map MvPolynomial.C - univU R m k * univW R m k).coeff i)

variable (R m k) in
/-- **The universal Mumford datum ring**: coefficients of a datum `(u, v, w)` with
`v² - f = u·w` and prescribed degree bounds, and nothing else. Every concrete datum over
an `R`-algebra arises by specialization (`ChabautyColeman.datumSpec`). -/
abbrev DatumRing : Type _ := MvPolynomial (MumfordVar m k) R ⧸ datumRelIdeal R f m k

variable (R m k) in
/-- The universal `u` over the datum ring. -/
noncomputable def datumU : (DatumRing R f m k)[X] :=
  (univU R m k).map (Ideal.Quotient.mk (datumRelIdeal R f m k))

variable (R m k) in
/-- The universal `v` over the datum ring. -/
noncomputable def datumV : (DatumRing R f m k)[X] :=
  (univV R m k).map (Ideal.Quotient.mk (datumRelIdeal R f m k))

variable (R m k) in
/-- The universal cofactor over the datum ring. -/
noncomputable def datumW : (DatumRing R f m k)[X] :=
  (univW R m k).map (Ideal.Quotient.mk (datumRelIdeal R f m k))

theorem datumV_degree : (datumV R f m k).degree < (m : WithBot ℕ) :=
  degree_map_le.trans_lt univV_degree

theorem datumW_degree : (datumW R f m k).degree < ((k : WithBot ℕ) + 1) :=
  degree_map_le.trans_lt univW_degree

/-- **The universal curve relation**: over the datum ring, `v² - f = u·w`. -/
theorem datumV_sq_sub :
    datumV R f m k ^ 2 - f.map (algebraMap R (DatumRing R f m k))
      = datumU R f m k * datumW R f m k := by
  have h0 : ((univV R m k) ^ 2 - f.map MvPolynomial.C
      - univU R m k * univW R m k).map (Ideal.Quotient.mk (datumRelIdeal R f m k)) = 0 := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_map] at h0
  have hC : (Ideal.Quotient.mk (datumRelIdeal R f m k)).comp
      (MvPolynomial.C : R →+* MvPolynomial (MumfordVar m k) R)
      = algebraMap R (DatumRing R f m k) := rfl
  rw [hC] at h0
  rw [datumV, datumU, datumW]
  linear_combination h0

section Nontrivial

variable [Nontrivial R]

private theorem degree_uSum_lt :
    (∑ i : Fin m, Polynomial.C ((MvPolynomial.X (uVar (k := k) i)
      : MvPolynomial (MumfordVar m k) R)) * Polynomial.X ^ (i : ℕ)).degree
      < (Polynomial.X ^ m : Polynomial (MvPolynomial (MumfordVar m k) R)).degree := by
  rw [degree_X_pow]
  exact degree_sum_fin_lt _

theorem univU_monic : (univU R m k).Monic :=
  (monic_X_pow m).add_of_left degree_uSum_lt

theorem univU_degree : (univU R m k).degree = (m : WithBot ℕ) := by
  rw [univU, degree_add_eq_left_of_degree_lt degree_uSum_lt, degree_X_pow]

theorem datumU_monic : (datumU R f m k).Monic :=
  univU_monic.map _

end Nontrivial

theorem datumU_natDegree [Nontrivial (DatumRing R f m k)] :
    (datumU R f m k).natDegree = m := by
  have : Nontrivial R := (algebraMap R (DatumRing R f m k)).domain_nontrivial
  have h : (datumU R f m k).degree = (m : WithBot ℕ) := by
    rw [datumU, univU_monic.degree_map, univU_degree]
  exact natDegree_eq_of_degree_eq_some h

section Spec

variable {A : Type*} [CommRing A] [Algebra R A] {u v w : A[X]}

variable (u v w) in
/-- The coordinate specialization at a concrete datum, on the polynomial level. -/
noncomputable def datumSpecAux : MvPolynomial (MumfordVar m k) R →ₐ[R] A :=
  MvPolynomial.aeval (elim (fun i ↦ u.coeff i) (fun i ↦ v.coeff i) fun i ↦ w.coeff i)

variable (u v w) in
/-- The coordinate specialization, as a ring homomorphism. -/
noncomputable def datumSpecRingHom : MvPolynomial (MumfordVar m k) R →+* A :=
  (datumSpecAux (R := R) (m := m) (k := k) u v w).toRingHom

@[simp] theorem datumSpecRingHom_X (s : MumfordVar m k) :
    datumSpecRingHom (R := R) u v w (MvPolynomial.X s)
      = elim (fun i ↦ u.coeff i) (fun i ↦ v.coeff i) (fun i ↦ w.coeff i) s := by
  rw [datumSpecRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, datumSpecAux,
    MvPolynomial.aeval_X]

@[simp] theorem datumSpecRingHom_X_uVar (i : Fin m) :
    datumSpecRingHom (R := R) (k := k) u v w (MvPolynomial.X (uVar i)) = u.coeff i := by
  rw [datumSpecRingHom_X, elim_uVar]

@[simp] theorem datumSpecRingHom_X_vVar (i : Fin m) :
    datumSpecRingHom (R := R) (k := k) u v w (MvPolynomial.X (vVar i)) = v.coeff i := by
  rw [datumSpecRingHom_X, elim_vVar]

@[simp] theorem datumSpecRingHom_X_wVar (i : Fin (k + 1)) :
    datumSpecRingHom (R := R) (m := m) u v w (MvPolynomial.X (wVar i)) = w.coeff i := by
  rw [datumSpecRingHom_X, elim_wVar]

theorem map_univV_datumSpecAux (hv : v.degree < (m : WithBot ℕ)) :
    (univV R m k).map (datumSpecRingHom (R := R) (m := m) (k := k) u v w) = v := by
  rw [univV, Polynomial.map_sum]
  have hsum : (∑ i : Fin m, (Polynomial.C (MvPolynomial.X (vVar (k := k) i))
        * Polynomial.X ^ (i : ℕ)).map
          (datumSpecRingHom (R := R) (m := m) (k := k) u v w))
      = ∑ i : Fin m, Polynomial.C (v.coeff i) * Polynomial.X ^ (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, datumSpecRingHom_X_vVar]
  rw [hsum]
  exact sum_C_coeff_mul_X_pow hv

theorem map_univW_datumSpecAux (hw : w.degree < ((k : WithBot ℕ) + 1)) :
    (univW R m k).map (datumSpecRingHom (R := R) (m := m) (k := k) u v w) = w := by
  rw [univW, Polynomial.map_sum]
  have hsum : (∑ i : Fin (k + 1), (Polynomial.C (MvPolynomial.X (wVar (m := m) i))
        * Polynomial.X ^ (i : ℕ)).map
          (datumSpecRingHom (R := R) (m := m) (k := k) u v w))
      = ∑ i : Fin (k + 1), Polynomial.C (w.coeff i) * Polynomial.X ^ (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, datumSpecRingHom_X_wVar]
  rw [hsum]
  exact sum_C_coeff_mul_X_pow (mod_cast hw)

variable [Nontrivial A]

theorem map_univU_datumSpecAux (hu : u.Monic) (hm : u.natDegree = m) :
    (univU R m k).map (datumSpecRingHom (R := R) (m := m) (k := k) u v w) = u := by
  rw [univU, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum]
  have hsum : (∑ i : Fin m, (Polynomial.C (MvPolynomial.X (uVar (k := k) i))
        * Polynomial.X ^ (i : ℕ)).map
          (datumSpecRingHom (R := R) (m := m) (k := k) u v w))
      = ∑ i : Fin m, Polynomial.C (u.coeff i) * Polynomial.X ^ (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, datumSpecRingHom_X_uVar]
  rw [hsum]
  have hdeg : (u - Polynomial.X ^ m).degree < (m : WithBot ℕ) := by
    have h := Polynomial.degree_sub_lt_left (by rw [degree_X_pow,
      Polynomial.degree_eq_natDegree hu.ne_zero, hm]) hu.ne_zero
      (by rw [hu.leadingCoeff, leadingCoeff_X_pow])
    rwa [Polynomial.degree_eq_natDegree hu.ne_zero, hm] at h
  have hsub : u - Polynomial.X ^ m
      = ∑ i : Fin m, Polynomial.C ((u - Polynomial.X ^ m).coeff i)
        * Polynomial.X ^ (i : ℕ) := (sum_C_coeff_mul_X_pow hdeg).symm
  have hcoeff : ∀ i : Fin m, (u - Polynomial.X ^ m).coeff i = u.coeff i := fun i ↦ by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right (by lia), sub_zero]
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [← hcoeff i], ← hsub]
  ring

theorem datumSpecRingHom_relIdeal (hu : u.Monic) (hm : u.natDegree = m)
    (hv : v.degree < (m : WithBot ℕ)) (hwd : w.degree < ((k : WithBot ℕ) + 1))
    (hw : v ^ 2 - f.map (algebraMap R A) = u * w) :
    ∀ a ∈ datumRelIdeal R f m k, datumSpecRingHom (R := R) (m := m) (k := k) u v w a
      = 0 := by
  intro a ha
  refine Submodule.span_induction ?_ (map_zero _) (fun x y _ _ hx hy ↦ by
    rw [map_add, hx, hy, add_zero]) (fun c x _ hx ↦ by
      rw [smul_eq_mul, map_mul, hx, mul_zero]) ha
  rintro x ⟨i, rfl⟩
  have h1 : ((univV R m k) ^ 2 - f.map MvPolynomial.C - univU R m k * univW R m k).map
      (datumSpecRingHom (R := R) (m := m) (k := k) u v w)
      = v ^ 2 - f.map (algebraMap R A) - u * w := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_map, map_univU_datumSpecAux hu hm, map_univV_datumSpecAux hv,
      map_univW_datumSpecAux hwd]
    rw [show (datumSpecRingHom (R := R) (m := m) (k := k) u v w).comp
        (MvPolynomial.C : R →+* MvPolynomial (MumfordVar m k) R) = algebraMap R A from
      RingHom.ext fun r ↦ (datumSpecAux (R := R) (m := m) (k := k) u v w).commutes r]
  have h2 : v ^ 2 - f.map (algebraMap R A) - u * w = 0 := by
    rw [hw]
    ring
  have h3 : (datumSpecRingHom (R := R) (m := m) (k := k) u v w)
      (((univV R m k) ^ 2 - f.map MvPolynomial.C - univU R m k * univW R m k).coeff i)
      = 0 := by
    rw [← Polynomial.coeff_map, h1.trans h2, Polynomial.coeff_zero]
  exact h3

variable (u v w) in
/-- **Specialization of the universal datum ring at a concrete Mumford datum**: any
`(u, v, w)` over an `R`-algebra with `v² - f = u·w` and the prescribed degree bounds
receives a unique coordinate homomorphism from the datum ring. -/
noncomputable def datumSpec (hu : u.Monic) (hm : u.natDegree = m)
    (hv : v.degree < (m : WithBot ℕ)) (hwd : w.degree < ((k : WithBot ℕ) + 1))
    (hw : v ^ 2 - f.map (algebraMap R A) = u * w) :
    DatumRing R f m k →+* A :=
  Ideal.Quotient.lift _ (datumSpecRingHom (R := R) (m := m) (k := k) u v w)
    (datumSpecRingHom_relIdeal f hu hm hv hwd hw)

theorem datumSpec_map_datumU (hu : u.Monic) (hm : u.natDegree = m)
    (hv : v.degree < (m : WithBot ℕ)) (hwd : w.degree < ((k : WithBot ℕ) + 1))
    (hw : v ^ 2 - f.map (algebraMap R A) = u * w) :
    (datumU R f m k).map (datumSpec f u v w hu hm hv hwd hw) = u := by
  rw [datumU, Polynomial.map_map, datumSpec, Ideal.Quotient.lift_comp_mk]
  exact map_univU_datumSpecAux hu hm

theorem datumSpec_map_datumV (hu : u.Monic) (hm : u.natDegree = m)
    (hv : v.degree < (m : WithBot ℕ)) (hwd : w.degree < ((k : WithBot ℕ) + 1))
    (hw : v ^ 2 - f.map (algebraMap R A) = u * w) :
    (datumV R f m k).map (datumSpec f u v w hu hm hv hwd hw) = v := by
  rw [datumV, Polynomial.map_map, datumSpec, Ideal.Quotient.lift_comp_mk]
  exact map_univV_datumSpecAux hv

theorem datumSpec_map_datumW (hu : u.Monic) (hm : u.natDegree = m)
    (hv : v.degree < (m : WithBot ℕ)) (hwd : w.degree < ((k : WithBot ℕ) + 1))
    (hw : v ^ 2 - f.map (algebraMap R A) = u * w) :
    (datumW R f m k).map (datumSpec f u v w hu hm hv hwd hw) = w := by
  rw [datumW, Polynomial.map_map, datumSpec, Ideal.Quotient.lift_comp_mk]
  exact map_univW_datumSpecAux hwd

end Spec

/-! ### Families of universal data -/

section Family

variable (R : Type*) [CommRing R] (f : R[X]) (ι : Type*) (m k : ℕ)

open MumfordVar MvPolynomial

/-- The relation ideal of a family of universal Mumford data, one coordinate block per
index. -/
noncomputable def datumRelIdealFam : Ideal (MvPolynomial (ι × MumfordVar m k) R) :=
  ⨆ i : ι, (datumRelIdeal R f m k).map (rename (Prod.mk i)).toRingHom

/-- **The universal ring of a family of Mumford data**, one block of coordinates per
index of `ι`, each satisfying the curve relation. -/
abbrev DatumFamRing : Type _ :=
  MvPolynomial (ι × MumfordVar m k) R ⧸ datumRelIdealFam R f ι m k

variable {ι}

/-- The `i`-th block inclusion into the family ring, on coordinates. -/
noncomputable def famBlockAux (i : ι) :
    MvPolynomial (MumfordVar m k) R →+* DatumFamRing R f ι m k :=
  (Ideal.Quotient.mk (datumRelIdealFam R f ι m k)).comp (rename (Prod.mk i)).toRingHom

theorem famBlockAux_relIdeal (i : ι) :
    ∀ a ∈ datumRelIdeal R f m k, famBlockAux R f m k i a = 0 := by
  intro a ha
  rw [famBlockAux, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  refine (le_iSup (fun j : ι ↦ (datumRelIdeal R f m k).map
    (rename (Prod.mk j)).toRingHom) i) ?_
  exact Ideal.mem_map_of_mem _ ha

/-- The `i`-th block inclusion `DatumRing → DatumFamRing`. -/
noncomputable def famBlock (i : ι) : DatumRing R f m k →+* DatumFamRing R f ι m k :=
  Ideal.Quotient.lift _ (famBlockAux R f m k i) (famBlockAux_relIdeal R f m k i)

/-- The `u`-polynomial of the `i`-th member of the universal family. -/
noncomputable def datumFamU (i : ι) : (DatumFamRing R f ι m k)[X] :=
  (datumU R f m k).map (famBlock R f m k i)

/-- The `v`-polynomial of the `i`-th member of the universal family. -/
noncomputable def datumFamV (i : ι) : (DatumFamRing R f ι m k)[X] :=
  (datumV R f m k).map (famBlock R f m k i)

/-- The cofactor polynomial of the `i`-th member of the universal family. -/
noncomputable def datumFamW (i : ι) : (DatumFamRing R f ι m k)[X] :=
  (datumW R f m k).map (famBlock R f m k i)

theorem famBlock_comp_algebraMap (i : ι) :
    (famBlock R f m k i).comp (algebraMap R (DatumRing R f m k))
      = algebraMap R (DatumFamRing R f ι m k) := by
  refine RingHom.ext fun r ↦ ?_
  change (famBlockAux R f m k i) (MvPolynomial.C r) = _
  rw [famBlockAux, RingHom.comp_apply]
  change Ideal.Quotient.mk _ ((rename (Prod.mk i)) (MvPolynomial.C r)) = _
  rw [rename_C]
  rfl

theorem datumFamU_monic [Nontrivial R] (i : ι) : (datumFamU R f m k i).Monic :=
  (datumU_monic f).map _

theorem datumFamU_natDegree [Nontrivial (DatumFamRing R f ι m k)] (i : ι) :
    (datumFamU R f m k i).natDegree = m := by
  have : Nontrivial R := (algebraMap R (DatumFamRing R f ι m k)).domain_nontrivial
  have : Nontrivial (DatumRing R f m k) := (famBlock R f m k i).domain_nontrivial
  rw [datumFamU, (datumU_monic f).natDegree_map, datumU_natDegree]

theorem datumFamV_degree (i : ι) :
    (datumFamV R f m k i).degree < (m : WithBot ℕ) :=
  degree_map_le.trans_lt (datumV_degree f)

theorem datumFamW_degree (i : ι) :
    (datumFamW R f m k i).degree < ((k : WithBot ℕ) + 1) :=
  degree_map_le.trans_lt (datumW_degree f)

/-- The curve relation for each member of the universal family. -/
theorem datumFamV_sq_sub (i : ι) :
    datumFamV R f m k i ^ 2 - f.map (algebraMap R (DatumFamRing R f ι m k))
      = datumFamU R f m k i * datumFamW R f m k i := by
  have h := congrArg (Polynomial.map (famBlock R f m k i)) (datumV_sq_sub (f := f)
    (m := m) (k := k))
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_map,
    famBlock_comp_algebraMap] at h
  exact h

section FamSpec

variable {R} {m k} {A : Type*} [CommRing A] [Algebra R A]
  {u v w : ι → A[X]}

variable (u v w) in
/-- The coordinate specialization of the family ring at a family of concrete data. -/
noncomputable def datumFamSpecAux : MvPolynomial (ι × MumfordVar m k) R →+* A :=
  (MvPolynomial.aeval fun p : ι × MumfordVar m k ↦
    Sum.elim (fun i : Fin m ↦ (u p.1).coeff i)
      (Sum.elim (fun i : Fin m ↦ (v p.1).coeff i)
        (fun i : Fin (k + 1) ↦ (w p.1).coeff i)) p.2 : _ →ₐ[R] A).toRingHom

theorem datumFamSpecAux_comp_rename (i : ι) :
    (datumFamSpecAux (R := R) (m := m) (k := k) u v w).comp
        (rename (Prod.mk i)).toRingHom
      = datumSpecRingHom (R := R) (m := m) (k := k) (u i) (v i) (w i) := by
  refine RingHom.ext fun x ↦ ?_
  change (MvPolynomial.aeval _) ((rename (Prod.mk i)) x) = (MvPolynomial.aeval _) x
  rw [MvPolynomial.aeval_rename]
  rfl

variable [Nontrivial A]

variable (u v w) in
/-- **Specialization of the family ring at a family of concrete Mumford data.** -/
noncomputable def datumFamSpec (hu : ∀ i, (u i).Monic) (hm : ∀ i, (u i).natDegree = m)
    (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) :
    DatumFamRing R f ι m k →+* A := by
  refine Ideal.Quotient.lift _ (datumFamSpecAux (R := R) (m := m) (k := k) u v w) fun a ha ↦ ?_
  have hle : datumRelIdealFam R f ι m k
      ≤ RingHom.ker (datumFamSpecAux (R := R) (m := m) (k := k) u v w) := by
    refine iSup_le fun i ↦ Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
      datumFamSpecAux_comp_rename]
    exact datumSpecRingHom_relIdeal f (hu i) (hm i) (hv i) (hwd i) (hw i) x hx
  exact hle ha

theorem datumFamSpec_comp_famBlock (hu : ∀ i, (u i).Monic)
    (hm : ∀ i, (u i).natDegree = m) (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (i : ι) :
    (datumFamSpec f u v w hu hm hv hwd hw).comp (famBlock R f m k i)
      = datumSpec f (u i) (v i) (w i) (hu i) (hm i) (hv i) (hwd i) (hw i) := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (datumFamSpec f u v w hu hm hv hwd hw) (famBlockAux R f m k i y) = _
  rw [famBlockAux, RingHom.comp_apply]
  change (datumFamSpecAux (R := R) (m := m) (k := k) u v w)
    ((rename (Prod.mk i)).toRingHom y) = _
  rw [← RingHom.comp_apply, datumFamSpecAux_comp_rename]
  rfl

/-- The family specialization restricts to the coefficients as the algebra map. -/
theorem datumFamSpec_comp_algebraMap (hu : ∀ i, (u i).Monic)
    (hm : ∀ i, (u i).natDegree = m) (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) :
    (datumFamSpec f u v w hu hm hv hwd hw).comp (algebraMap R (DatumFamRing R f ι m k))
      = algebraMap R A := by
  refine RingHom.ext fun r ↦ ?_
  change datumFamSpecAux (R := R) (m := m) (k := k) u v w (MvPolynomial.C r) = _
  change (MvPolynomial.aeval _) (MvPolynomial.C r) = _
  exact MvPolynomial.aeval_C ..

theorem datumFamSpec_map_datumFamU (hu : ∀ i, (u i).Monic)
    (hm : ∀ i, (u i).natDegree = m) (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (i : ι) :
    (datumFamU R f m k i).map (datumFamSpec f u v w hu hm hv hwd hw) = u i := by
  rw [datumFamU, Polynomial.map_map, datumFamSpec_comp_famBlock]
  exact datumSpec_map_datumU f (hu i) (hm i) (hv i) (hwd i) (hw i)

theorem datumFamSpec_map_datumFamV (hu : ∀ i, (u i).Monic)
    (hm : ∀ i, (u i).natDegree = m) (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (i : ι) :
    (datumFamV R f m k i).map (datumFamSpec f u v w hu hm hv hwd hw) = v i := by
  rw [datumFamV, Polynomial.map_map, datumFamSpec_comp_famBlock]
  exact datumSpec_map_datumV f (hu i) (hm i) (hv i) (hwd i) (hw i)

theorem datumFamSpec_map_datumFamW (hu : ∀ i, (u i).Monic)
    (hm : ∀ i, (u i).natDegree = m) (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (i : ι) :
    (datumFamW R f m k i).map (datumFamSpec f u v w hu hm hv hwd hw) = w i := by
  rw [datumFamW, Polynomial.map_map, datumFamSpec_comp_famBlock]
  exact datumSpec_map_datumW f (hu i) (hm i) (hv i) (hwd i) (hw i)

/-- The value of the family-ring specialization on a `u`-coordinate. -/
theorem datumFamSpec_mk_X_uVar (hu : ∀ i, (u i).Monic) (hm : ∀ i, (u i).natDegree = m)
    (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (b : ι) (i : Fin m) :
    datumFamSpec f u v w hu hm hv hwd hw
        (Ideal.Quotient.mk _ (MvPolynomial.X (R := R) (b, (Sum.inl i : MumfordVar m k))))
      = (u b).coeff i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X _) = _
  rw [MvPolynomial.aeval_X]
  rfl

/-- The value of the family-ring specialization on a `v`-coordinate. -/
theorem datumFamSpec_mk_X_vVar (hu : ∀ i, (u i).Monic) (hm : ∀ i, (u i).natDegree = m)
    (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (b : ι) (i : Fin m) :
    datumFamSpec f u v w hu hm hv hwd hw
        (Ideal.Quotient.mk _ (MvPolynomial.X (R := R)
          (b, (Sum.inr (Sum.inl i) : MumfordVar m k))))
      = (v b).coeff i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X _) = _
  rw [MvPolynomial.aeval_X]
  rfl

/-- The value of the family-ring specialization on a `w`-coordinate. -/
theorem datumFamSpec_mk_X_wVar (hu : ∀ i, (u i).Monic) (hm : ∀ i, (u i).natDegree = m)
    (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (b : ι) (i : Fin (k + 1)) :
    datumFamSpec f u v w hu hm hv hwd hw
        (Ideal.Quotient.mk _ (MvPolynomial.X (R := R)
          (b, (Sum.inr (Sum.inr i) : MumfordVar m k))))
      = (w b).coeff i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X _) = _
  rw [MvPolynomial.aeval_X]
  rfl

/-- The value of the family-ring specialization on a constant. -/
theorem datumFamSpec_mk_C (hu : ∀ i, (u i).Monic) (hm : ∀ i, (u i).natDegree = m)
    (hv : ∀ i, (v i).degree < (m : WithBot ℕ))
    (hwd : ∀ i, (w i).degree < ((k : WithBot ℕ) + 1))
    (hw : ∀ i, v i ^ 2 - f.map (algebraMap R A) = u i * w i) (r : R) :
    datumFamSpec f u v w hu hm hv hwd hw (Ideal.Quotient.mk _ (MvPolynomial.C r))
      = algebraMap R A r := by
  change (MvPolynomial.aeval _) (MvPolynomial.C r) = _
  exact MvPolynomial.aeval_C ..

end FamSpec

end Family

end ChabautyColeman

end
