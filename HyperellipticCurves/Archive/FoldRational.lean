/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Log.Fold.FoldAssemble
public import HyperellipticCurves.Log.Ftau.DeltaRational
public import Mathlib.RingTheory.Localization.Away.Basic

import HyperellipticCurves.Curve.TraceMatrix
import HyperellipticCurves.ForMathlib.Resultant
import HyperellipticCurves.Log.Fold.FoldTrace

/-!
# Rational invariant differentials at the fold (the denominator layer)

`ChabautyColeman.invariantDiffFold_rational`: the entries of the differential matrix
`M(X) = (∂F_τ/∂Y)(X, 0)` of the fold form of the translated formal group law are images
of universal elements of the localized three-block family ring
(`ChabautyColeman.DatumFamRing`) under the chart-data specialization
(`ChabautyColeman.ftauFamSpec`), specialized at `Y = 0`. Its consumer is the global inverse
differential matrix of `HyperellipticCurves.Archive.GlobalDiff`; the main theorems do not
depend on this file.

Rather than running the pipeline generically (with reduction chains, chain-length bookkeeping
and generic-degree control), the fold reads `M` off the `Y = 0` invariance identity of the
trace form (`ChabautyColeman.sum_traceMat_mul_setYZero_pderiv_FtauFold`): `T(X)·M(X) = T₂`
with `T` the trace matrix of the `X`-side chart block and `T₂` the constant trace matrix of
the `τ`-datum — both matrices are functions of the *starting data* alone, so `M = T⁻¹·T₂` by
Cramer over the family ring localized away from **four denominators**: the three block
resultants `Res(Uᵢ, 2Vᵢ)` and the determinant of the (resultant-scaled) generic trace matrix.
All four specialize to units *unconditionally* — their residues are nonzero by coprimality of
the `τ`-datum (its own Bézout certificate) and nondegeneracy of the trace matrix
(`ChabautyColeman.det_traceMatrix_ne_zero`) — so no residue-side genericity clause (centre
certificates, avoidance, chain lengths) is needed, and the consumer receives `hprod` outright.

The generic pipeline machinery of `HyperellipticCurves.Log.Cantor.GenericPipeline` is not
needed at the fold shape.

Blueprint node: `lem:delta-rational`, rationality clause.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-- Each member of a list is a unit in the localization away from the list's product. -/
theorem isUnit_algebraMap_away_prod {R : Type*} [CommRing R] {den : List R} {x : R}
    (hx : x ∈ den) : IsUnit (algebraMap R (Localization.Away den.prod) x) :=
  IsLocalization.Away.isUnit_of_dvd (S := Localization.Away den.prod) (x := den.prod)
    (List.dvd_prod hx)

section Helpers

variable {L : Type*} [CommRing L]

/-- Left cancellation of a square matrix with unit determinant. -/
private theorem matrix_mul_left_cancel {n : ℕ} {T A B : Matrix (Fin n) (Fin n) L}
    (hdet : IsUnit T.det) (h : T * A = T * B) : A = B := by
  have h2 := congrArg (T⁻¹ * ·) h
  simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul T hdet] using h2

/-- A resultant-scaled Bézout cofactor computes the `r`-multiple of the trace matrix. -/
private theorem traceMat_eq_mul_of_scaled {U V p q c t : L[X]} {r : L}
    (hU : U.Monic) (hq : U * p + 2 * V * q = C r) (ht : c * U + t * (2 * V) = 1)
    (i j : ℕ) : traceMat U q i j = r * traceMat U t i j := by
  have h1 : 2 * V * (q - C r * t) = U * (C r * c - p) := by
    linear_combination hq - C r * ht
  have hcop : IsCoprime U (2 * V) := ⟨c, t, ht⟩
  have hdvd : U ∣ q - C r * t :=
    hcop.dvd_of_dvd_mul_left ⟨C r * c - p, by linear_combination h1⟩
  have h2 : traceMat U q i j = traceMat U (C r * t) i j := by
    obtain ⟨e, he⟩ := hdvd
    refine congrArg Neg.neg (topCoeffMod_congr hU ⟨X ^ (i + j) * e, ?_⟩)
    linear_combination X ^ (i + j) * he
  rw [h2, traceMat, show X ^ (i + j) * (C r * t) = C r * (X ^ (i + j) * t) from by ring,
    topCoeffMod_C_mul, traceMat]
  ring

/-- The determinant of a trace-matrix block maps along ring homomorphisms. -/
private theorem det_traceMat_matrix_map {S : Type*} [CommRing S] [Nontrivial S]
    (ψ : L →+* S) {U q : L[X]} (hU : U.Monic) (n : ℕ) :
    ψ (Matrix.of fun i j : Fin n ↦ traceMat U q (i : ℕ) (j : ℕ)).det
      = (Matrix.of fun i j : Fin n ↦ traceMat (U.map ψ) (q.map ψ) (i : ℕ) (j : ℕ)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact (traceMat_map ψ hU q (i : ℕ) (j : ℕ)).symm

end Helpers

section Det

variable {K : Type*} [Field K]

/-- Over a field, the trace matrix at a resultant-scaled cofactor has nonzero
determinant: the scale is the nonzero resultant, and the descaled matrix is the
nondegenerate trace matrix of the datum. -/
private theorem det_traceMat_scaled_ne_zero {U V p q : K[X]} {r : K} {n : ℕ}
    (hU : U.Monic) (hn : U.natDegree = n) (hr : r ≠ 0)
    (hq : U * p + 2 * V * q = C r) :
    (Matrix.of fun i j : Fin n ↦ traceMat U q (i : ℕ) (j : ℕ)).det ≠ 0 := by
  -- the true cofactor
  set t : K[X] := C r⁻¹ * q with hto
  have ht : (C r⁻¹ * p) * U + t * (2 * V) = 1 := by
    have h := congrArg (C r⁻¹ * ·) hq
    simp only [mul_add, ← map_mul, inv_mul_cancel₀ hr, map_one] at h
    linear_combination h
  -- the scaled matrix
  have hscale : (Matrix.of fun i j : Fin n ↦ traceMat U q (i : ℕ) (j : ℕ))
      = r • Matrix.of fun i j : Fin n ↦ traceMat U t (i : ℕ) (j : ℕ) := by
    ext i j
    exact traceMat_eq_mul_of_scaled hU hq ht i j
  -- the descaled matrix is the reindexed nondegenerate trace matrix
  have hre : (Matrix.of fun i j : Fin n ↦ traceMat U t (i : ℕ) (j : ℕ))
      = (Matrix.reindex (finCongr hn) (finCongr hn)) (traceMatrix U t) := by
    ext i j
    simp [traceMatrix, Matrix.reindex_apply]
  have hcop : IsCoprime U t := ⟨C r⁻¹ * p, 2 * V, by linear_combination ht⟩
  rw [hscale, Matrix.det_smul, hre, Matrix.det_reindex_self, Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero n hr) (det_traceMatrix_ne_zero hU hcop)

end Det

section Units

variable {O : Type*} [CommRing O] [IsLocalRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

include hu hne in
/-- The residue of a generic block resultant under the chart-data specialization is the
resultant of the reduced `τ`-datum. -/
private theorem resSpec_residue (bb : Fin 3) :
    mvSeriesResidue (Fin n ⊕ Fin n) O (ftauFamSpec hu hne hv hw hbez
        ((datumFamU O f n (ftauKBound f n) bb).resultant
          (2 * datumFamV O f n (ftauKBound f n) bb) n n))
      = (u.map (residue O)).resultant (2 * v.map (residue O)) n n := by
  set χρ : DatumFamRing O f (Fin 3) n (ftauKBound f n) →+* ResidueField O :=
    (mvSeriesResidue (Fin n ⊕ Fin n) O).comp (ftauFamSpec hu hne hv hw hbez) with hχρ
  have hρU : (datumFamU O f n (ftauKBound f n) bb).map χρ = u.map (residue O) := by
    rw [hχρ, ← Polynomial.map_map, ftauFamSpec_map_datumFamU hu hne hv hw hbez bb]
    exact ftauFamU_map_mvSeriesResidue bb
  have hρ2V : (2 * datumFamV O f n (ftauKBound f n) bb).map χρ
      = 2 * v.map (residue O) := by
    rw [Polynomial.map_mul, Polynomial.map_ofNat, hχρ, ← Polynomial.map_map,
      ftauFamSpec_map_datumFamV hu hne hv hw hbez bb]
    rw [ftauFamV_map_mvSeriesResidue hu hne hv hw hbez bb]
  rw [show mvSeriesResidue (Fin n ⊕ Fin n) O (ftauFamSpec hu hne hv hw hbez _)
      = χρ _ from rfl, ← hρU, ← hρ2V]
  exact (Polynomial.resultant_map_map _ _ n n χρ).symm

include hu hne hv hbez in
/-- The reduced `τ`-datum's resultant is nonzero: its own Bézout certificate descends. -/
private theorem residue_resultant_ne_zero :
    (u.map (residue O)).resultant (2 * v.map (residue O)) n n ≠ 0 := by
  have hcopρ : IsCoprime (u.map (residue O)) (2 * v.map (residue O)) := by
    refine ⟨c₁.map (residue O), c₂.map (residue O), ?_⟩
    have h := congrArg (Polynomial.map (residue O)) hbez
    simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_ofNat] using h
  have h2vdeg : (2 * v.map (residue O)).natDegree ≤ n := by
    refine natDegree_mul_le.trans ?_
    simpa using natDegree_map_le.trans (natDegree_le_iff_degree_le.mpr
      (hv.le.trans_eq (by rw [degree_eq_natDegree hu.ne_zero, hne])))
  have h := isUnit_resultant_of_isCoprime (hu.map (residue O)) h2vdeg hcopρ
  rw [hu.natDegree_map, hne] at h
  exact h.ne_zero

include hv hw hbez in
/-- The generic block resultants specialize to units. -/
private theorem isUnit_ftauFamSpec_res (bb : Fin 3) :
    IsUnit (ftauFamSpec hu hne hv hw hbez
      ((datumFamU O f n (ftauKBound f n) bb).resultant
        (2 * datumFamV O f n (ftauKBound f n) bb) n n)) := by
  refine isUnit_of_mvSeriesResidue_ne_zero _ _ ?_
  rw [resSpec_residue hu hne hv hw hbez bb]
  exact residue_resultant_ne_zero hu hne hv hbez

include hv hw hbez in
/-- The determinant of the resultant-scaled generic trace matrix of the `X`-side block
specializes to a unit: its residue is a nonzero multiple of the nondegenerate trace
matrix determinant of the reduced `τ`-datum. -/
private theorem isUnit_ftauFamSpec_det
    {p q : (DatumFamRing O f (Fin 3) n (ftauKBound f n))[X]}
    (he : datumFamU O f n (ftauKBound f n) 0 * p
        + 2 * datumFamV O f n (ftauKBound f n) 0 * q
      = C ((datumFamU O f n (ftauKBound f n) 0).resultant
          (2 * datumFamV O f n (ftauKBound f n) 0) n n)) :
    IsUnit (ftauFamSpec hu hne hv hw hbez
      (Matrix.of fun i j : Fin n ↦
        traceMat (datumFamU O f n (ftauKBound f n) 0) q (i : ℕ) (j : ℕ)).det) := by
  have : Nontrivial (DatumFamRing O f (Fin 3) n (ftauKBound f n)) :=
    (ftauFamSpec hu hne hv hw hbez).domain_nontrivial
  set χρ : DatumFamRing O f (Fin 3) n (ftauKBound f n) →+* ResidueField O :=
    (mvSeriesResidue (Fin n ⊕ Fin n) O).comp (ftauFamSpec hu hne hv hw hbez) with hχρ
  have hρU : (datumFamU O f n (ftauKBound f n) 0).map χρ = u.map (residue O) := by
    rw [hχρ, ← Polynomial.map_map, ftauFamSpec_map_datumFamU hu hne hv hw hbez 0]
    exact ftauFamU_map_mvSeriesResidue 0
  have hρ2V : (2 * datumFamV O f n (ftauKBound f n) 0).map χρ
      = 2 * v.map (residue O) := by
    rw [Polynomial.map_mul, Polynomial.map_ofNat, hχρ, ← Polynomial.map_map,
      ftauFamSpec_map_datumFamV hu hne hv hw hbez 0]
    rw [ftauFamV_map_mvSeriesResidue hu hne hv hw hbez 0]
  refine isUnit_of_mvSeriesResidue_ne_zero _ _ ?_
  rw [show mvSeriesResidue (Fin n ⊕ Fin n) O (ftauFamSpec hu hne hv hw hbez _)
      = χρ _ from rfl,
    det_traceMat_matrix_map χρ (datumFamU_monic O f n (ftauKBound f n) 0) n]
  have hqρ : (u.map (residue O)) * p.map χρ + 2 * v.map (residue O) * q.map χρ
      = C (χρ ((datumFamU O f n (ftauKBound f n) 0).resultant
          (2 * datumFamV O f n (ftauKBound f n) 0) n n)) := by
    have h := congrArg (Polynomial.map χρ) he
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      hρU, hρ2V] at h
    linear_combination h
  have h := det_traceMat_scaled_ne_zero (n := n) (hu.map (residue O))
    (by rw [hu.natDegree_map, hne])
    (by rw [show χρ _ = mvSeriesResidue (Fin n ⊕ Fin n) O
          (ftauFamSpec hu hne hv hw hbez _) from rfl, resSpec_residue hu hne hv hw hbez 0]
        exact residue_resultant_ne_zero hu hne hv hbez) hqρ
  rw [hρU]
  exact h

end Units

section Rational

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsDomain O]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
  (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
  (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
  (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
  {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)

/-- **Rational invariant differentials at the fold** (blueprint `lem:delta-rational`,
rationality clause): the entries of the differential matrix `M(X) = (∂F_τ/∂Y)(X, 0)` of the
fold form of the translated formal group law are images of universal elements of the localized
three-block family ring under the `Y = 0` chart-data specialization — so they can be
re-specialized along any rational family of Mumford data. The denominators specialize to units
*unconditionally*, so no residue-side genericity clause is needed. -/
theorem invariantDiffFold_rational (hn0 : n ≠ 0)
    (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    (hav : IsFtauFoldAvoid A a b hu hne hv hw hbez d) :
    ∃ (den : List (DatumFamRing O f (Fin 3) n (ftauKBound f n)))
      (hprod : IsUnit (ftauFamSpec hu hne hv hw hbez den.prod))
      (M' : Fin n → Fin n → Localization.Away den.prod),
      ∀ i j, (ftauFoldFGL hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hπ hπ0
          hsplit hunit).diffMatrix i j
        = setYZero (IsLocalization.Away.lift (S := Localization.Away den.prod)
            den.prod hprod (M' i j)) := by
  classical
  set φ : DatumFamRing O f (Fin 3) n (ftauKBound f n) →+* MvPowerSeries (Fin n ⊕ Fin n) O :=
    ftauFamSpec hu hne hv hw hbez with hφ
  have : Nontrivial (DatumFamRing O f (Fin 3) n (ftauKBound f n)) := φ.domain_nontrivial
  -- the generic blocks and their specializations
  set Ub : Fin 3 → (DatumFamRing O f (Fin 3) n (ftauKBound f n))[X] :=
    datumFamU O f n (ftauKBound f n) with hUbdef
  set Vb : Fin 3 → (DatumFamRing O f (Fin 3) n (ftauKBound f n))[X] :=
    datumFamV O f n (ftauKBound f n) with hVbdef
  have hUmap (bb : Fin 3) : (Ub bb).map φ = ftauFamU u n bb :=
    ftauFamSpec_map_datumFamU hu hne hv hw hbez bb
  have hVmap (bb : Fin 3) : (Vb bb).map φ = ftauFamV hu hne hv hw hbez bb :=
    ftauFamSpec_map_datumFamV hu hne hv hw hbez bb
  have hUm (bb : Fin 3) : (Ub bb).Monic := datumFamU_monic O f n (ftauKBound f n) bb
  have hUdeg (bb : Fin 3) : (Ub bb).natDegree = n :=
    datumFamU_natDegree O f n (ftauKBound f n) bb
  have hVdeg (bb : Fin 3) : (Vb bb).natDegree ≤ n :=
    natDegree_le_iff_degree_le.mpr (datumFamV_degree O f n (ftauKBound f n) bb).le
  have h2V (bb : Fin 3) : (2 * Vb bb).natDegree ≤ n :=
    natDegree_mul_le.trans (by simpa using hVdeg bb)
  -- the resultant denominators and the scaled block-0 certificate
  set res : Fin 3 → DatumFamRing O f (Fin 3) n (ftauKBound f n) :=
    fun bb ↦ (Ub bb).resultant (2 * Vb bb) n n with hresdef
  obtain ⟨p₀, q₀, -, -, he₀⟩ := exists_mul_add_mul_eq_C_resultant (Ub 0) (2 * Vb 0)
    (hUdeg 0).le (h2V 0) (Or.inl hn0)
  set D : DatumFamRing O f (Fin 3) n (ftauKBound f n) :=
    (Matrix.of fun i j : Fin n ↦ traceMat (Ub 0) q₀ (i : ℕ) (j : ℕ)).det with hDdef
  have hresunit (bb : Fin 3) : IsUnit (φ (res bb)) :=
    isUnit_ftauFamSpec_res hu hne hv hw hbez bb
  have hDunit : IsUnit (φ D) := isUnit_ftauFamSpec_det hu hne hv hw hbez he₀
  -- the denominator list
  set den : List (DatumFamRing O f (Fin 3) n (ftauKBound f n)) :=
    [res 0, res 1, res 2, D] with hden
  have hmem_res (bb : Fin 3) : res bb ∈ den := by fin_cases bb <;> simp [hden]
  have hmemD : D ∈ den := by simp [hden]
  have hprod : IsUnit (φ den.prod) := by
    rw [hden, List.prod_cons, List.prod_cons, List.prod_cons, List.prod_singleton,
      map_mul, map_mul, map_mul]
    exact (hresunit 0).mul ((hresunit 1).mul ((hresunit 2).mul hDunit))
  -- the localized generic trace matrices
  set α : DatumFamRing O f (Fin 3) n (ftauKBound f n)
      →+* Localization.Away den.prod := algebraMap _ _ with hα
  have : Nontrivial (Localization.Away den.prod) :=
    (IsLocalization.Away.lift (S := Localization.Away den.prod)
      den.prod hprod).domain_nontrivial
  have hresL (bb : Fin 3) : IsUnit (((Ub bb).map α).resultant ((2 * Vb bb).map α) n n) := by
    rw [Polynomial.resultant_map_map]
    exact isUnit_algebraMap_away_prod (hmem_res bb)
  obtain ⟨c₀', t₀, -, -, hbez₀⟩ := exists_bezout_of_isUnit_resultant
    (natDegree_map_le.trans (hUdeg 0).le) (natDegree_map_le.trans (h2V 0))
    (Or.inl hn0) (hresL 0)
  obtain ⟨c₁', t₁, -, -, hbez₁⟩ := exists_bezout_of_isUnit_resultant
    (natDegree_map_le.trans (hUdeg 1).le) (natDegree_map_le.trans (h2V 1))
    (Or.inl hn0) (hresL 1)
  obtain ⟨c₂', t₂, -, -, hbez₂⟩ := exists_bezout_of_isUnit_resultant
    (natDegree_map_le.trans (hUdeg 2).le) (natDegree_map_le.trans (h2V 2))
    (Or.inl hn0) (hresL 2)
  rw [Polynomial.map_mul, Polynomial.map_ofNat] at hbez₀ hbez₁ hbez₂
  set T : Matrix (Fin n) (Fin n) (Localization.Away den.prod) :=
    Matrix.of fun i j ↦ traceMat ((Ub 0).map α) t₀ (i : ℕ) (j : ℕ) with hTdef
  set T₂ : Matrix (Fin n) (Fin n) (Localization.Away den.prod) :=
    Matrix.of fun i j ↦ traceMat ((Ub 2).map α) t₂ (i : ℕ) (j : ℕ) with hT₂def
  -- the determinant of `T` is a unit: `α D` is, and it is `α (res 0) ^ n · det T`
  have hqα : ((Ub 0).map α) * p₀.map α + 2 * ((Vb 0).map α) * q₀.map α
      = C (α (res 0)) := by
    have h := congrArg (Polynomial.map α) he₀
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_ofNat] at h
    linear_combination h
  have hDdet : α D = α (res 0) ^ n * T.det := by
    rw [hDdef, det_traceMat_matrix_map α (hUm 0) n,
      show (Matrix.of fun i j : Fin n ↦ traceMat ((Ub 0).map α) (q₀.map α) (i : ℕ) (j : ℕ))
        = α (res 0) • T from Matrix.ext fun i j ↦
          traceMat_eq_mul_of_scaled ((hUm 0).map α) hqα hbez₀ (i : ℕ) (j : ℕ),
      Matrix.det_smul, Fintype.card_fin]
  have hdetT : IsUnit T.det :=
    isUnit_of_mul_isUnit_right (hDdet ▸ isUnit_algebraMap_away_prod hmemD)
  -- the generic identity `T · (T⁻¹ · T₂) = T₂`
  have hTM : T * (T⁻¹ * T₂) = T₂ := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv T hdetT, Matrix.one_mul]
  refine ⟨den, hprod, fun i j ↦ (T⁻¹ * T₂) i j, fun i j ↦ ?_⟩
  set Φ : Localization.Away den.prod →+* MvPowerSeries (Fin n ⊕ Fin n) O :=
    IsLocalization.Away.lift den.prod hprod with hΦdef
  have hΦα : Φ.comp α = φ := IsLocalization.Away.lift_comp den.prod hprod
  -- the concrete `Y`-side certificate, from the block-1 generic one
  have hmapΦ (P : (DatumFamRing O f (Fin 3) n (ftauKBound f n))[X]) :
      (P.map α).map Φ = P.map φ := by
    rw [Polynomial.map_map, hΦα]
  have hsYc : (c₁'.map Φ) * ftauUY u n
      + (t₁.map Φ) * (2 * ftauVY hu hne hv hw hbez) = 1 := by
    have h := congrArg (Polynomial.map Φ) hbez₁
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one,
      Polynomial.map_mul, Polynomial.map_ofNat, hmapΦ, hmapΦ, hUmap 1, hVmap 1] at h
    exact h
  -- the output certificate, from the fold avoidance
  obtain ⟨cP, sP, hsP⟩ := isCoprime_ftauFoldPipe hu hne hv hw hbez hav
  have hainj : Function.Injective a := fun i' j' h ↦ by
    by_contra hne'
    exact not_isUnit_zero (sub_eq_zero.mpr h ▸ hunit i' j' hne')
  -- the `Y = 0` invariance identity, as a matrix identity
  set Mdiff : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) O) :=
    Matrix.of fun jj k ↦ setYZero
      (MvPowerSeries.pderiv (Sum.inr k) (FtauFold A a b hu hne hv hw hbez d jj))
    with hMdiffdef
  set TS4 : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) O) :=
    Matrix.of fun i jj : Fin n ↦ traceMat (chartU u n) (sP.map setYZero) (i : ℕ) (jj : ℕ)
    with hTS4def
  set TC : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) O) :=
    Matrix.of fun i k : Fin n ↦ MvPowerSeries.C (traceMat u c₂ (i : ℕ) (k : ℕ))
    with hTCdef
  have hS4m : TS4 * Mdiff = TC := by
    refine Matrix.ext fun i k ↦ ?_
    rw [Matrix.mul_apply, hTS4def, hMdiffdef, hTCdef]
    simp only [Matrix.of_apply]
    exact sum_traceMat_mul_setYZero_pderiv_FtauFold_eq_C hu hne hv hw hbez hf hfdeg hroot
      hcc ha hb hd hπ hπ0 hsplit hainj hsYc
      (sum_traceMat_ftauFoldPipe hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hunit hav
        k i.isLt hsYc hsP)
  -- the `Y = 0` specialization of the generic identity
  set χ : Localization.Away den.prod →+* MvPowerSeries (Fin n) O :=
    (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O).comp Φ
    with hχdef
  have hmapχ (P : (DatumFamRing O f (Fin 3) n (ftauKBound f n))[X]) :
      (P.map α).map χ = (P.map φ).map setYZero := by
    rw [Polynomial.map_map, hχdef, RingHom.comp_assoc, hΦα, ← Polynomial.map_map]
  have hchartU : ((Ub 0).map α).map χ = chartU u n := by
    rw [hmapχ, hUmap 0]
    exact ftauUX_map_setYZero
  have hchartV : ((Vb 0).map α).map χ = chartV hu hne.ge hv hw hbez := by
    rw [hmapχ, hVmap 0]
    exact ftauVX_map_setYZero hu hne hv hw hbez
  have hUC : ((Ub 2).map α).map χ
      = u.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) := by
    rw [hmapχ, hUmap 2, show ftauFamU u n 2 = u.map MvPowerSeries.C from rfl,
      Polynomial.map_map, setYZero_comp_C]
  have hVC : ((Vb 2).map α).map χ
      = v.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) := by
    rw [hmapχ, hVmap 2, show ftauFamV hu hne hv hw hbez 2 = v.map MvPowerSeries.C from rfl,
      Polynomial.map_map, setYZero_comp_C]
  have hcert₀χ : (c₀'.map χ) * chartU u n
      + (t₀.map χ) * (2 * chartV hu hne.ge hv hw hbez) = 1 := by
    have h := congrArg (Polynomial.map χ) hbez₀
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one,
      Polynomial.map_mul, Polynomial.map_ofNat, hchartU, hchartV] at h
    exact h
  have hcert₂χ : (c₂'.map χ)
        * u.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)
      + (t₂.map χ) * (2 * v.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)) = 1 := by
    have h := congrArg (Polynomial.map χ) hbez₂
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one,
      Polynomial.map_mul, Polynomial.map_ofNat, hUC, hVC] at h
    exact h
  have hχT : χ.mapMatrix T = TS4 := by
    refine Matrix.ext fun i jj ↦ ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hTdef, hTS4def]
    simp only [Matrix.of_apply]
    rw [← traceMat_map χ ((hUm 0).map α) t₀, hchartU]
    exact traceMat_congr (chartU_monic hu hne.ge) hcert₀χ
      (bezout_ftauFoldPipe_map_setYZero hu hne hv hw hbez hf hfdeg hroot hcc hb hd hπ hπ0
        hsplit hainj hsP) (i : ℕ) (jj : ℕ)
  have hχT₂ : χ.mapMatrix T₂ = TC := by
    refine Matrix.ext fun i k ↦ ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hT₂def, hTCdef]
    simp only [Matrix.of_apply]
    rw [← traceMat_map χ ((hUm 2).map α) t₂, hUC,
      ← traceMat_map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) hu c₂]
    have hcertC : (c₁.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O))
          * u.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)
        + (c₂.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O))
          * (2 * v.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)) = 1 := by
      have h := congrArg (Polynomial.map (MvPowerSeries.C :
        O →+* MvPowerSeries (Fin n) O)) hbez
      simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_ofNat] using h
    exact traceMat_congr (hu.map _) hcert₂χ hcertC (i : ℕ) (k : ℕ)
  -- cancellation
  have hχTM : TS4 * χ.mapMatrix (T⁻¹ * T₂) = TC := by
    rw [← hχT, ← hχT₂, ← map_mul]
    exact congrArg _ hTM
  have hdetTS4 : IsUnit TS4.det := by
    rw [← hχT, ← RingHom.map_det]
    exact hdetT.map χ
  have hMd : Mdiff = χ.mapMatrix (T⁻¹ * T₂) :=
    matrix_mul_left_cancel hdetTS4 (hS4m.trans hχTM.symm)
  -- read off the entry
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) O) ↦
    M i j) hMd
  simp only [hMdiffdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    at hentry
  change MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0)
    (MvPowerSeries.pderiv (Sum.inr j) (FtauFold A a b hu hne hv hw hbez d i)) = _
  rw [← setYZero_apply]
  exact hentry

end Rational

end ChabautyColeman

end
