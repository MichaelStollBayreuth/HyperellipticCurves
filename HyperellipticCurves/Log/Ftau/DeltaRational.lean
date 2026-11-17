/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.UnivDatum
public import HyperellipticCurves.Log.Analytic.Lam
public import HyperellipticCurves.Log.Cantor.GenericPipeline
public import HyperellipticCurves.Log.Ftau.FtauAssoc
public import HyperellipticCurves.Log.Ftau.FtauCerts

/-!
# The three-block family ring for `F_τ` (towards `lem:delta-rational`)

The family layer of `lem:delta-rational`: the three-block family ring of
`HyperellipticCurves.Curve.UnivDatum` specialized at the two transported chart data and the
`τ`-datum. `ChabautyColeman.ftauFamU`/`ftauFamV`/`ftauFamW` are the three block data as
family polynomials, `ChabautyColeman.ftauFamSpec` the specialization homomorphism to
`MvPowerSeries (Fin n ⊕ Fin n) O`, and `ChabautyColeman.ftauKBound` the degree bound of
the family ring. These feed the trace-matrix route to `lem:delta-rational`
(`ChabautyColeman.invariantDiffFold_rational`, `HyperellipticCurves.Archive.FoldRational`) and the
chart-diff files (`HyperellipticCurves.Archive.GlobalDiff` and its Weierstrass/infinity siblings).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section GenericSpec

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

/-- The `u`-parts of the three-block concrete data: the two transported chart polynomials
and the `τ`-datum's `u`. -/
noncomputable def ftauFamU (u' : O[X]) (n' : ℕ) :
    Fin 3 → Polynomial (MvPowerSeries (Fin n' ⊕ Fin n') O) :=
  ![ftauUX u' n', ftauUY u' n', u'.map MvPowerSeries.C]

variable [Nontrivial O]

/-- The `v`-parts of the three-block concrete data: the two transported chart square roots
and the `τ`-datum's `v`. -/
noncomputable def ftauFamV : Fin 3 → Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) :=
  ![ftauVX hu hne hv hw hbez, ftauVY hu hne hv hw hbez, v.map MvPowerSeries.C]

/-- The cofactor parts of the three-block concrete data: the cofactors of the two chart
blocks and the `τ`-datum's `w`. -/
noncomputable def ftauFamW : Fin 3 → Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) :=
  ![cantorCofactor (f.map MvPowerSeries.C) (ftauUX u n) (ftauVX hu hne hv hw hbez),
    cantorCofactor (f.map MvPowerSeries.C) (ftauUY u n) (ftauVY hu hne hv hw hbez),
    w.map MvPowerSeries.C]

include hu hne in
theorem ftauFamU_monic (i : Fin 3) : (ftauFamU u n i).Monic := by
  fin_cases i
  · exact chartU_map_rename_monic Sum.inl hu hne.ge
  · exact chartU_map_rename_monic Sum.inr hu hne.ge
  · exact hu.map _

include hu hne in
theorem ftauFamU_natDegree (i : Fin 3) : (ftauFamU u n i).natDegree = n := by
  fin_cases i
  · exact (chartU_map_rename_natDegree Sum.inl hu hne.ge).trans hne
  · exact (chartU_map_rename_natDegree Sum.inr hu hne.ge).trans hne
  · exact (hu.natDegree_map _).trans hne

theorem ftauFamV_degree (i : Fin 3) :
    (ftauFamV hu hne hv hw hbez i).degree < (n : WithBot ℕ) := by
  have hdeg : u.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree hu.ne_zero, hne]
  have hchart : (chartV hu hne.ge hv hw hbez).degree < (n : WithBot ℕ) :=
    (chartV_degree_lt hu hne.ge hv hw hbez).trans_eq hdeg
  fin_cases i
  · exact degree_map_le.trans_lt hchart
  · exact degree_map_le.trans_lt hchart
  · exact degree_map_le.trans_lt (hv.trans_eq hdeg)

theorem ftauFamW_sq_sub (i : Fin 3) :
    ftauFamV hu hne hv hw hbez i ^ 2
        - f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = ftauFamU u n i * ftauFamW hu hne hv hw hbez i := by
  fin_cases i
  · exact cantorCofactor_spec _ (chartU_map_rename_monic Sum.inl hu hne.ge)
      (chartV_map_rename_dvd hu hne hv hw hbez Sum.inl)
  · exact cantorCofactor_spec _ (chartU_map_rename_monic Sum.inr hu hne.ge)
      (chartV_map_rename_dvd hu hne hv hw hbez Sum.inr)
  · have h := congrArg (Polynomial.map
      (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)) hw
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul] at h

theorem ftauFamW_degree (i : Fin 3) :
    (ftauFamW hu hne hv hw hbez i).degree < ((ftauKBound f n : WithBot ℕ) + 1) := by
  refine degree_lt_add_one_of_natDegree_le ?_
  have hbound : ∀ i, (ftauFamW hu hne hv hw hbez i).natDegree
      ≤ max (2 * ((ftauFamU u n i).natDegree - 1))
          (f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).natDegree
        - (ftauFamU u n i).natDegree := fun i ↦
    natDegree_cofactor_le_of_sq_sub (ftauFamU_monic hu hne i)
      (by rw [ftauFamU_natDegree hu hne]; exact ftauFamV_degree hu hne hv hw hbez i)
      (ftauFamW_sq_sub hu hne hv hw hbez i)
  refine (hbound i).trans ?_
  rw [ftauFamU_natDegree hu hne, ftauKBound]
  exact Nat.sub_le_sub_right (max_le_max le_rfl natDegree_map_le) n

/-- The curve relation for the three-block data, in the algebra-map spelling. -/
theorem ftauFamW_sq_sub' (i : Fin 3) :
    ftauFamV hu hne hv hw hbez i ^ 2
        - f.map (algebraMap O (MvPowerSeries (Fin n ⊕ Fin n) O))
      = ftauFamU u n i * ftauFamW hu hne hv hw hbez i := by
  rw [← MvPowerSeries.c_eq_algebraMap]
  exact ftauFamW_sq_sub hu hne hv hw hbez i

/-- **The chart-data specialization**: the three-block family ring specializes at the
two transported chart data and the `τ`-datum. -/
noncomputable def ftauFamSpec :
    DatumFamRing O f (Fin 3) n (ftauKBound f n)
      →+* MvPowerSeries (Fin n ⊕ Fin n) O :=
  datumFamSpec (f := f) (u := ftauFamU u n) (v := ftauFamV hu hne hv hw hbez)
    (w := ftauFamW hu hne hv hw hbez) (ftauFamU_monic hu hne) (ftauFamU_natDegree hu hne)
    (ftauFamV_degree hu hne hv hw hbez) (ftauFamW_degree hu hne hv hw hbez)
    (ftauFamW_sq_sub' hu hne hv hw hbez)

theorem ftauFamSpec_map_datumFamU (i : Fin 3) :
    (datumFamU O f n (ftauKBound f n) i).map (ftauFamSpec hu hne hv hw hbez)
      = ftauFamU u n i :=
  datumFamSpec_map_datumFamU (f := f) _ _ _ _ _ i

theorem ftauFamSpec_map_datumFamV (i : Fin 3) :
    (datumFamV O f n (ftauKBound f n) i).map (ftauFamSpec hu hne hv hw hbez)
      = ftauFamV hu hne hv hw hbez i :=
  datumFamSpec_map_datumFamV (f := f) _ _ _ _ _ i

theorem ftauFamSpec_comp_algebraMap :
    (ftauFamSpec hu hne hv hw hbez).comp
        (algebraMap O (DatumFamRing O f (Fin 3) n (ftauKBound f n)))
      = MvPowerSeries.C := by
  rw [ftauFamSpec, datumFamSpec_comp_algebraMap, ← MvPowerSeries.c_eq_algebraMap]

section Catalog

open MumfordVar MvPowerSeries

/-- The values of the chart-data specialization on the coordinates. -/
theorem ftauFamSpec_mk_X_uVar (b : Fin 3) (i : Fin n) :
    ftauFamSpec hu hne hv hw hbez
        (Ideal.Quotient.mk _ (MvPolynomial.X (R := O) (b,
          (Sum.inl i : MumfordVar n (ftauKBound f n)))))
      = (ftauFamU u n b).coeff i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X _) = _
  rw [MvPolynomial.aeval_X]
  rfl

theorem ftauFamSpec_mk_X_vVar (b : Fin 3) (i : Fin n) :
    ftauFamSpec hu hne hv hw hbez
        (Ideal.Quotient.mk _ (MvPolynomial.X (R := O) (b,
          (Sum.inr (Sum.inl i) : MumfordVar n (ftauKBound f n)))))
      = (ftauFamV hu hne hv hw hbez b).coeff i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X _) = _
  rw [MvPolynomial.aeval_X]
  rfl

theorem ftauFamSpec_mk_X_wVar (b : Fin 3) (i : Fin (ftauKBound f n + 1)) :
    ftauFamSpec hu hne hv hw hbez
        (Ideal.Quotient.mk _ (MvPolynomial.X (R := O) (b,
          (Sum.inr (Sum.inr i) : MumfordVar n (ftauKBound f n)))))
      = (ftauFamW hu hne hv hw hbez b).coeff i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X _) = _
  rw [MvPolynomial.aeval_X]
  rfl

end Catalog

end GenericSpec

section GenericSpecLocal

variable {O : Type*} [CommRing O] [IsLocalRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

private theorem map_mvSeriesResidue (p : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) :
    p.map (mvSeriesResidue (Fin n ⊕ Fin n) O)
      = (p.map MvPowerSeries.constantCoeff).map (residue O) :=
  (Polynomial.map_map _ _ p).symm

/-- The three `u`-parts of the concrete chart data all reduce to the `τ`-datum's `u`. -/
theorem ftauFamU_map_mvSeriesResidue (i : Fin 3) :
    (ftauFamU u n i).map (mvSeriesResidue (Fin n ⊕ Fin n) O) = u.map (residue O) := by
  fin_cases i
  · change (ftauUX u n).map _ = _
    rw [map_mvSeriesResidue, ftauUX_map_constantCoeff]
  · change (ftauUY u n).map _ = _
    rw [map_mvSeriesResidue, ftauUY_map_constantCoeff]
  · change (u.map MvPowerSeries.C).map _ = _
    rw [map_mvSeriesResidue, map_C_map_constantCoeff]

/-- The three `v`-parts of the concrete chart data all reduce to the `τ`-datum's `v`. -/
theorem ftauFamV_map_mvSeriesResidue (i : Fin 3) :
    (ftauFamV hu hne hv hw hbez i).map (mvSeriesResidue (Fin n ⊕ Fin n) O)
      = v.map (residue O) := by
  fin_cases i
  · change (ftauVX hu hne hv hw hbez).map _ = _
    rw [map_mvSeriesResidue, ftauVX_map_constantCoeff]
  · change (ftauVY hu hne hv hw hbez).map _ = _
    rw [map_mvSeriesResidue, ftauVY_map_constantCoeff]
  · change (v.map MvPowerSeries.C).map _ = _
    rw [map_mvSeriesResidue, map_C_map_constantCoeff]

end GenericSpecLocal

end ChabautyColeman

end
