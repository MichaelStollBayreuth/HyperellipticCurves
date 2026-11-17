/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.RingTheory.Polynomial.Resultant.Basic`: separability
-- (`Mathlib.FieldTheory.Separable`) and residue fields of local rings
-- (`Mathlib.RingTheory.LocalRing.ResidueField.Basic`), for the statements of the separability
-- criteria, and `Polynomial.degreeLT` with the division by a monic polynomial on it (the mirror
-- `HyperellipticCurves.Mathlib.RingTheory.Polynomial.Quotient`), for the Sylvester blocks.
public import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

-- For the proofs only.
import HyperellipticCurves.Mathlib.Algebra.Polynomial.Div
import HyperellipticCurves.Mathlib.Data.Nat.Choose.Vandermonde
import HyperellipticCurves.Mathlib.RingTheory.Polynomial.Basic

/-!
# Bézout certificates, the discriminant at a given degree, and the Sylvester block form

If the `(m, n)`-resultant of `u` and `g` is a unit, then `s * u + t * g = 1` is solvable with
`deg s < n`, `deg t < m`; read for `g = f'` this is a separability certificate.

`Polynomial.discrOfDegree f n` is the discriminant of `f` viewed as a polynomial of degree `n`
(the discriminant of the binary form `Z ^ n * f (X / Z)`): Mathlib's discriminant matrix
`Polynomial.sylvesterDeriv` with the degree replaced by `n`. It is a polynomial in the
coefficients of `f` up to degree `n`, so it commutes with every ring homomorphism, and the
**drop-by-one formula** — proved by expanding the modified Sylvester matrix along its normalized
last row, whose two minors are padded Sylvester matrices — identifies it with `discr f`,
`leadingCoeff f ^ 2 * discr f` or `0` according to the degree of `f`.

Let `g` be monic over a commutative ring `R`, `m = g.natDegree`, and let
`S : R[X]_m × R[X]_n →ₗ R[X]_(m + n)`, `(u, v) ↦ g * v + p * u`, be the Sylvester map of `g`
and `p` (`Polynomial.sylvesterMap`), whose matrix is the Sylvester matrix. For `p = 1` it is a
linear equivalence `Ψ`, with inverse `q ↦ (q %ₘ g, q /ₘ g)`, and `B = Ψ⁻¹ ∘ₗ S` is the
endomorphism `(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`. In the product of
the monomial bases its matrix is block lower triangular with diagonal blocks the matrix of
multiplication by `p` modulo `g` and `1`. No signs appear: `B` is an endomorphism, so the two
blocks are never reordered. This is the linear algebra behind `AdjoinRoot.norm_mk_eq_resultant`.

## Main definitions

* `Polynomial.sylvesterDerivOfDegree`: `Polynomial.sylvesterDeriv` for `f` viewed as a
  polynomial of degree `n`.
* `Polynomial.discrOfDegree`: the discriminant of `f` viewed as a polynomial of degree `n`.
* `Polynomial.mulModByMonic`: multiplication by `p` on `R[X]_m`, `q ↦ (p * q) %ₘ g`.
* `Polynomial.sylvesterEquivOne`: the Sylvester map `Ψ` of `g` and `1`, as a linear equivalence.
* `Polynomial.sylvesterBlock`: the endomorphism `B = Ψ⁻¹ ∘ₗ S`.

## Main statements

* `Polynomial.exists_bezout_of_isUnit_resultant`: a degree-controlled Bézout certificate from a
  unit resultant (compare `Polynomial.isUnit_resultant_iff_isCoprime`), and
  `Polynomial.isUnit_resultant_of_isCoprime` its converse at a monic first member.
* `Polynomial.separable_of_isUnit_resultant`: a polynomial whose resultant with its derivative is
  a unit is separable, and `Polynomial.separable_map_of_separable_residue` the consequence over a
  local ring: separability of the reduction of a monic polynomial lifts through any ring
  homomorphism out of the local ring.
* `Polynomial.det_submatrix_sylvester_succ_left`, `Polynomial.det_submatrix_sylvester_succ_right`:
  two minors of Sylvester matrices are padded resultants.
* `Polynomial.discrOfDegree_map`: the discriminant at a fixed degree commutes with every ring
  homomorphism.
* `Polynomial.discrOfDegree_add_two`: **drop-by-one formula**,
  `discrOfDegree f (n + 2) = coeff f (n + 1) ^ 2 * discrOfDegree f (n + 1)` for `deg f ≤ n + 1`.
* `Polynomial.discr_map`, `Polynomial.Monic.discr_map`: the discriminant commutes with a
  degree-preserving ring homomorphism.
* `Polynomial.isUnit_discr_iff_separable`, `Polynomial.Monic.isUnit_discr_iff`: for a unit
  leading coefficient, the discriminant is a unit if and only if the polynomial is separable.
* `Polynomial.resultant_C_sub_X`: `Res(f, C x - X) = f(x)`.
* `Polynomial.Monic.resultant_one_right`: `Res(g, 1) = 1` for monic `g`.
* `Polynomial.sylvesterMap_one_comp_sylvesterBlock`: `Ψ ∘ₗ B = S`.
* `Polynomial.toMatrix_sylvesterBlock`: the block form of the matrix of `B`.
* `Polynomial.det_sylvesterBlock`: `det B = det (Polynomial.mulModByMonic hg p)`.
* `Polynomial.eval_dvd_resultant_of_eval_eq_zero`: the value of `q` at a root of `g` divides
  `Res(g, q)`.
* `Polynomial.resultant_sq_add_mul_right`,
  `Polynomial.isSquare_leadingCoeff_pow_mul_resultant_of_dvd_sq_sub`: `Res(a, f)` for
  `f ≡ b ^ 2` modulo `a` is a square up to a power of `lc(a)`.
* `Polynomial.discr_ne_zero_of_isCoprime_derivative`: a polynomial prime to its derivative over a
  domain has a nonzero discriminant.
* `Polynomial.Monic.discr_mul`: `disc (f g) = disc f * disc g * Res(f, g) ^ 2` for monic `f` and
  `g`, from `Polynomial.Monic.resultant_derivative_mul`, `Res(f, (f g)') = Res(f, f') Res(f, g)`.
* `Polynomial.separable_of_discr_ne_zero`: a polynomial over a field with nonzero discriminant is
  separable.
* `Polynomial.discr_map_of_injective`: the discriminant commutes with injective ring
  homomorphisms.

The Sylvester material is vendored from EllipticCurves (`EllipticCurves/Mathlib/Basic.lean`).

Auxiliary material for the formalization of the Chabauty–Coleman bound and of `2`-descent for
hyperelliptic curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] {u g : R[X]} {m n : ℕ}

/-- **Bézout certificate from a unit resultant**, with degree control: if the
`(m, n)`-resultant of `u` and `g` is a unit, there are `s, t` with
`s·u + t·g = 1`, `deg s < n` and `deg t < m`. -/
theorem exists_bezout_of_isUnit_resultant (hu : u.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (H : m ≠ 0 ∨ n ≠ 0) (hres : IsUnit (u.resultant g m n)) :
    ∃ s t : R[X], s.degree < (n : WithBot ℕ) ∧ t.degree < (m : WithBot ℕ)
      ∧ s * u + t * g = 1 := by
  obtain ⟨p, q, hp, hq, he⟩ := exists_mul_add_mul_eq_C_resultant u g hu hg H
  obtain ⟨c, hc⟩ := hres.exists_left_inv
  have hCle : ∀ r : R[X], (C c * r).degree ≤ r.degree := fun r ↦
    calc (C c * r).degree ≤ (C c).degree + r.degree := degree_mul_le _ _
      _ ≤ 0 + r.degree := by gcongr; exact degree_C_le
      _ = r.degree := zero_add _
  refine ⟨C c * p, C c * q, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (hCle p) hp
  · exact lt_of_le_of_lt (hCle q) hq
  · calc C c * p * u + C c * q * g = C c * (u * p + g * q) := by ring
      _ = 1 := by rw [he, ← map_mul, hc, map_one]

/-- **A coprime pair has unit resultant**, at the exact degree of the monic member and any
degree bound for the other: the converse supplier for
`Polynomial.exists_bezout_of_isUnit_resultant`. -/
theorem isUnit_resultant_of_isCoprime (hu : u.Monic) (hg : g.natDegree ≤ n)
    (hcop : IsCoprime u g) : IsUnit (u.resultant g u.natDegree n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = g.natDegree + k := ⟨n - g.natDegree, by lia⟩
  rw [resultant_add_right_deg u g u.natDegree g.natDegree k le_rfl, coeff_natDegree,
    hu.leadingCoeff, one_pow, one_mul]
  exact (isUnit_resultant_iff_isCoprime hu).mpr hcop

/-- **A polynomial with unit resultant `Res(f, f')` is separable**: the Bézout certificate of
`Polynomial.exists_bezout_of_isUnit_resultant` is a separability certificate. -/
theorem separable_of_isUnit_resultant {f : R[X]} {d : ℕ} (hf : f.natDegree ≤ d) (hd : d ≠ 0)
    (hres : IsUnit (f.resultant f.derivative d d)) : f.Separable :=
  let ⟨s, t, _, _, hst⟩ := exists_bezout_of_isUnit_resultant hf
    ((natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hf)) (.inl hd) hres
  ⟨s, t, hst⟩

open IsLocalRing in
/-- **Separability of the reduction lifts through a local ring**: if the reduction of a
monic polynomial `f` of positive degree over a local ring `O` modulo the maximal ideal is
separable, then the image of `f` under any ring homomorphism out of `O` is separable — the
residue resultant of `f` with `f'` is a unit, hence the resultant of `f` with `f'` is a
unit in `O` and its image provides the Bézout certificate. -/
theorem separable_map_of_separable_residue {O : Type*} [CommRing O] [IsLocalRing O]
    {S : Type*} [CommRing S] (φ : O →+* S) {f : O[X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hsep : (f.map (residue O)).Separable) : (f.map φ).Separable := by
  set d := f.natDegree
  have hres : IsUnit ((f.map (residue O)).resultant (f.map (residue O)).derivative
      (f.map (residue O)).natDegree d) :=
    isUnit_resultant_of_isCoprime (hf.map _)
      ((natDegree_derivative_le _).trans (by rw [hf.natDegree_map]; exact Nat.sub_le _ _)) hsep
  rw [hf.natDegree_map, derivative_map, resultant_map_map _ _ d d] at hres
  have hresO : IsUnit (f.resultant f.derivative d d) :=
    notMem_maximalIdeal.mp fun hm ↦ hres.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hm)
  refine separable_of_isUnit_resultant natDegree_map_le hd.ne' ?_
  rw [derivative_map, resultant_map_map _ _ d d]
  exact hresO.map φ

/-! ### Minors of Sylvester matrices -/

section minors

variable {f : R[X]}

/-- Deleting the last row and the last `g`-column of `sylvester f g (m + 1) (n + 1)` leaves
`sylvester f g m (n + 1)` when `f` has degree at most `m`. -/
theorem det_submatrix_sylvester_succ_left (hf : f.natDegree ≤ m) :
    ((sylvester f g (m + 1) (n + 1)).submatrix (Fin.last _).succAbove
      ((Fin.last m).castAdd (n + 1)).succAbove).det = resultant f g m (n + 1) := by
  rw [resultant, ← Matrix.det_reindex_self (finCongr (show m + 1 + n = m + (n + 1) by lia))]
  congr 1
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply,
    Fin.succAbove_last]
  induction j using Fin.addCases with
  | left j =>
    rw [show ((Fin.last m).castAdd (n + 1)).succAbove (Fin.cast _ (j.castAdd (n + 1))) =
        (Fin.castSucc j).castAdd (n + 1) from ?_]
    · simp [sylvester, Fin.addCases_left]
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
      exact Fin.ext rfl
  | right j =>
    rw [show ((Fin.last m).castAdd (n + 1)).succAbove (Fin.cast _ (j.natAdd m)) =
        j.natAdd (m + 1) from ?_]
    · simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Fin.val_castSucc, Fin.val_cast,
        Set.mem_Icc]
      split_ifs <;> first | rfl | lia | exact coeff_eq_zero_of_natDegree_lt (by lia)
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def])]
      exact Fin.ext (by simp; lia)

/-- Deleting the last row and the last column of `sylvester f g m (n + 1)` leaves
`sylvester f g m n` when `g` has degree at most `n`. -/
theorem det_submatrix_sylvester_succ_right (hg : g.natDegree ≤ n) :
    ((sylvester f g m (n + 1)).submatrix (Fin.last _).succAbove (Fin.last _).succAbove).det =
      resultant f g m n := by
  rw [resultant]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_last]
  induction j using Fin.addCases with
  | left j =>
    rw [show Fin.castSucc (j.castAdd n) = j.castAdd (n + 1) from Fin.ext rfl]
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.val_castSucc, Set.mem_Icc]
    split_ifs <;> first | rfl | lia | exact coeff_eq_zero_of_natDegree_lt (by lia)
  | right j =>
    rw [show Fin.castSucc (j.natAdd m) = (Fin.castSucc j).natAdd m from Fin.ext rfl]
    simp [sylvester, Fin.addCases_right]

end minors

/-! ### The discriminant of a polynomial viewed as a polynomial of given degree -/

section discr

variable {S : Type*} [CommRing S] {f : R[X]}

/-- `Polynomial.sylvesterDeriv` for `f` viewed as a polynomial of degree `n`: the Sylvester matrix
of `f'` and `f` padded to the degrees `n - 1` and `n`, with the last row normalized as in
`Polynomial.sylvesterDeriv`. At `n = f.natDegree` it is `f.sylvesterDeriv` definitionally. -/
noncomputable def sylvesterDerivOfDegree (f : R[X]) (n : ℕ) :
    Matrix (Fin (n - 1 + n)) (Fin (n - 1 + n)) R :=
  if hn : n = 0 then 0
  else (f.derivative.sylvester f (n - 1) n).updateRow ⟨2 * n - 2, by lia⟩
    (fun j ↦ if ↑j = n - 2 then 1 else if ↑j = 2 * n - 2 then (n : R) else 0)

theorem sylvesterDerivOfDegree_natDegree (f : R[X]) :
    f.sylvesterDerivOfDegree f.natDegree = f.sylvesterDeriv := rfl

lemma sylvesterDerivOfDegree_map (φ : R →+* S) (f : R[X]) (n : ℕ) :
    (f.map φ).sylvesterDerivOfDegree n = φ.mapMatrix (f.sylvesterDerivOfDegree n) := by
  simp only [sylvesterDerivOfDegree]
  split_ifs
  · simp
  · rw [RingHom.mapMatrix_apply, Matrix.map_updateRow, derivative_map, sylvester_map_map,
      RingHom.mapMatrix_apply]
    congr 1
    ext j
    simp [apply_ite φ]

/-- `sylvesterDerivOfDegree f (n + 2)` in the form used to expand its determinant: the last row is
the unit vector at the last `f`-column plus `n + 2` times the unit vector at the last
`f'`-column. -/
lemma sylvesterDerivOfDegree_add_two (f : R[X]) (n : ℕ) :
    f.sylvesterDerivOfDegree (n + 2) =
      (f.derivative.sylvester f (n + 1) (n + 1 + 1)).updateRow (Fin.last _)
        (Pi.single ((Fin.last n).castAdd (n + 1 + 1)) 1 +
          ((n + 2 : ℕ) : R) • Pi.single (Fin.last _) 1) := by
  ext i j
  rw [sylvesterDerivOfDegree, dite_eq_right (by lia)]
  simp only [Matrix.updateRow_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff,
    Fin.val_castAdd, Fin.val_last, Nat.add_eq, smul_eq_mul]
  split_ifs <;> first | rfl | lia | simp

/-- The discriminant of `f` viewed as a polynomial of degree `n`, i.e. the discriminant of the
binary form `Z ^ n * f (X / Z)` of degree `n` (for `f.natDegree ≤ n`): the determinant of
`Polynomial.sylvesterDerivOfDegree f n`, with the sign convention of `Polynomial.discr`. It depends
only on the coefficients of `f` in degrees `≤ n`, hence commutes with every ring homomorphism
(`Polynomial.discrOfDegree_map`); it equals `f.discr` at `n = f.natDegree`,
`f.leadingCoeff ^ 2 * f.discr` at `n = f.natDegree + 1` and `0` for larger `n`
(`Polynomial.discrOfDegree_add_two`). -/
noncomputable def discrOfDegree (f : R[X]) (n : ℕ) : R :=
  (f.sylvesterDerivOfDegree n).det * (-1) ^ (n * (n - 1) / 2)

@[simp]
theorem discrOfDegree_natDegree (f : R[X]) : f.discrOfDegree f.natDegree = f.discr := rfl

theorem discrOfDegree_of_natDegree_eq (h : f.natDegree = n) : f.discrOfDegree n = f.discr :=
  h ▸ rfl

@[simp] theorem discrOfDegree_zero (f : R[X]) : f.discrOfDegree 0 = 1 := by
  simp [discrOfDegree, sylvesterDerivOfDegree]

@[simp] theorem discrOfDegree_one (f : R[X]) : f.discrOfDegree 1 = 1 := by
  simp [discrOfDegree, sylvesterDerivOfDegree, Matrix.det_unique]

/-- The discriminant at a fixed degree commutes with every ring homomorphism (in contrast to
`Polynomial.discr_map`, which needs the degree to be preserved). -/
theorem discrOfDegree_map (φ : R →+* S) (f : R[X]) (n : ℕ) :
    (f.map φ).discrOfDegree n = φ (f.discrOfDegree n) := by
  rw [discrOfDegree, discrOfDegree, sylvesterDerivOfDegree_map, ← RingHom.map_det]
  simp

private lemma det_sylvesterDerivOfDegree_add_two (hf : f.natDegree ≤ n + 1) :
    (f.sylvesterDerivOfDegree (n + 2)).det =
      (-1) ^ (n + 1) * f.coeff (n + 1) * resultant f.derivative f n (n + 1) := by
  have hf' : f.derivative.natDegree ≤ n := (natDegree_derivative_le f).trans (by lia)
  rw [sylvesterDerivOfDegree_add_two, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    ← Matrix.adjugate_apply, ← Matrix.adjugate_apply, Matrix.adjugate_fin_succ_eq_det_submatrix,
    Matrix.adjugate_fin_succ_eq_det_submatrix, det_submatrix_sylvester_succ_left hf',
    det_submatrix_sylvester_succ_right hf, resultant_add_right_deg f.derivative f n (n + 1) 1 hf,
    resultant_add_left_deg f.derivative f n (n + 1) (k := 1) hf', coeff_derivative]
  have h1 : (-1 : R) ^ (n + 1 + (n + 1) + n) = (-1) ^ n := by
    rw [show n + 1 + (n + 1) + n = n + 2 * (n + 1) by ring, pow_add, pow_mul]
    simp
  have h2 : (-1 : R) ^ (n + 1 + (n + 1) + (n + 1 + (n + 1))) = 1 := by
    rw [show n + 1 + (n + 1) + (n + 1 + (n + 1)) = 2 * (2 * (n + 1)) by ring, pow_mul]
    simp
  simp only [Fin.val_last, Fin.val_castAdd, Nat.add_eq, h1, h2, pow_one]
  push_cast
  ring

/-- **Drop-by-one formula**: the discriminant of `f` as a polynomial of degree `n + 2` is the
square of its coefficient in degree `n + 1` times its discriminant as a polynomial of degree
`n + 1`. (This fails for `n + 1` in place of `n + 2`: `discrOfDegree (C c) 1 = 1`.) -/
theorem discrOfDegree_add_two (hf : f.natDegree ≤ n + 1) :
    f.discrOfDegree (n + 2) = f.coeff (n + 1) ^ 2 * f.discrOfDegree (n + 1) := by
  rw [discrOfDegree, det_sylvesterDerivOfDegree_add_two hf]
  rcases hf.lt_or_eq with hlt | heq
  · simp [coeff_eq_zero_of_natDegree_lt hlt]
  have hres := resultant_deriv (natDegree_pos_iff_degree_pos.mp (show 0 < f.natDegree by lia))
  rw [heq, Nat.add_sub_cancel] at hres
  have hlc : f.coeff (n + 1) = f.leadingCoeff := by rw [leadingCoeff, heq]
  have hexp : (n + 2) * (n + 2 - 1) / 2 = (n + 1) * n / 2 + (n + 1) := by
    rw [show n + 2 - 1 = n + 1 from rfl, show (n + 2) * (n + 1) = (n + 1) * n + (n + 1) * 2 by ring,
      Nat.add_mul_div_right _ _ two_pos]
  rw [resultant_comm, hres, ← discrOfDegree_of_natDegree_eq heq, hlc, hexp, pow_add,
    (Nat.even_mul_succ_self n).neg_one_pow]
  have hs : (-1 : R) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have ht : (-1 : R) ^ ((n + 1) * n / 2) * (-1) ^ ((n + 1) * n / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (f.leadingCoeff ^ 2 * f.discrOfDegree (n + 1) *
    ((-1 : R) ^ ((n + 1) * n / 2)) ^ 2) * hs + (f.leadingCoeff ^ 2 * f.discrOfDegree (n + 1)) * ht

/-- The discriminant of a nonconstant `f` as a polynomial of degree `natDegree f + 1` is
`leadingCoeff f ^ 2 * discr f`. -/
theorem discrOfDegree_natDegree_add_one (hf : 0 < f.natDegree) :
    f.discrOfDegree (f.natDegree + 1) = f.leadingCoeff ^ 2 * f.discr := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hf.ne'
  rw [hk, discrOfDegree_add_two hk.le, ← hk, coeff_natDegree, discrOfDegree_natDegree]

theorem discrOfDegree_eq_zero_of_natDegree_add_two_le (h : f.natDegree + 2 ≤ n) :
    f.discrOfDegree n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by lia⟩
  rw [discrOfDegree_add_two (by lia), coeff_eq_zero_of_natDegree_lt (by lia)]
  simp

theorem le_natDegree_add_one_of_isUnit_discrOfDegree [Nontrivial R]
    (h : IsUnit (f.discrOfDegree n)) : n ≤ f.natDegree + 1 := by
  by_contra! hn
  exact h.ne_zero (discrOfDegree_eq_zero_of_natDegree_add_two_le hn)

/-- For a polynomial with unit leading coefficient, the discriminant as a polynomial of degree
`natDegree f` or `natDegree f + 1` is a unit if and only if the discriminant is. -/
theorem isUnit_discrOfDegree_iff_isUnit_discr (hn : f.natDegree ≤ n) (hn' : n ≤ f.natDegree + 1)
    (hlc : IsUnit f.leadingCoeff) : IsUnit (f.discrOfDegree n) ↔ IsUnit f.discr := by
  rcases hn.eq_or_lt with rfl | hlt
  · rw [discrOfDegree_natDegree]
  obtain rfl : n = f.natDegree + 1 := by lia
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0
    simp
  · rw [discrOfDegree_natDegree_add_one h0, (hlc.pow 2).mul_left_iff]

/-- If the discriminant of `f` as a polynomial of some degree `≥ natDegree f` is a unit, so is the
discriminant of `f`. -/
theorem isUnit_discr_of_isUnit_discrOfDegree (hf : f.natDegree ≤ n)
    (h : IsUnit (f.discrOfDegree n)) : IsUnit f.discr := by
  rcases lt_or_ge n (f.natDegree + 2) with hn | hn
  · rcases hf.eq_or_lt with rfl | hlt
    · rwa [discrOfDegree_natDegree] at h
    obtain rfl : n = f.natDegree + 1 := by lia
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0
      simp
    · rw [discrOfDegree_natDegree_add_one h0] at h
      exact (IsUnit.mul_iff.mp h).2
  · rw [discrOfDegree_eq_zero_of_natDegree_add_two_le hn, isUnit_zero_iff] at h
    have := subsingleton_of_zero_eq_one h
    exact isUnit_of_subsingleton _

/-- If the discriminant of a nonconstant `f` as a polynomial of degree `natDegree f + 1` is a unit,
its leading coefficient is a unit. -/
theorem isUnit_leadingCoeff_of_isUnit_discrOfDegree (hf : 0 < f.natDegree)
    (h : IsUnit (f.discrOfDegree (f.natDegree + 1))) : IsUnit f.leadingCoeff := by
  rw [discrOfDegree_natDegree_add_one hf, IsUnit.mul_iff, isUnit_pow_iff two_ne_zero] at h
  exact h.1

/-- The discriminant commutes with a ring homomorphism that preserves the degree. -/
theorem discr_map (φ : R →+* S) (h : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  rw [← discrOfDegree_natDegree, h, discrOfDegree_map, discrOfDegree_natDegree]

/-- The discriminant of a monic polynomial commutes with any ring homomorphism into a nontrivial
ring. -/
theorem Monic.discr_map (hf : f.Monic) (φ : R →+* S) [Nontrivial S] :
    (f.map φ).discr = φ f.discr :=
  Polynomial.discr_map φ (hf.natDegree_map φ)

/-- For a monic polynomial, the padded resultant `Res(f, f', n, n - 1)` of
`Polynomial.resultant_deriv` is a unit if and only if `f` is separable. The padding matters: in
characteristic dividing `n` the derivative has degree below `n - 1`. -/
lemma Monic.isUnit_resultant_derivative_iff (hf : f.Monic) :
    IsUnit (resultant f f.derivative f.natDegree (f.natDegree - 1)) ↔ f.Separable := by
  obtain ⟨k, hk⟩ : ∃ k, f.natDegree - 1 = f.derivative.natDegree + k :=
    ⟨_, (Nat.add_sub_cancel' (natDegree_derivative_le f)).symm⟩
  rw [hk, resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree k le_rfl,
    hf.coeff_natDegree, one_pow, one_mul, isUnit_resultant_iff_isCoprime hf, ← separable_def]

/-- A polynomial with unit leading coefficient has unit discriminant if and only if it is
separable. -/
theorem isUnit_discr_iff_separable (hlc : IsUnit f.leadingCoeff) :
    IsUnit f.discr ↔ f.Separable := by
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0
    rw [leadingCoeff_C] at hlc
    simp [separable_C, hlc]
  obtain ⟨c, hc⟩ := hlc.exists_left_inv
  have hcu : IsUnit c := .of_mul_eq_one _ hc
  have hmonic : (C c * f).Monic := by rw [Monic.def, leadingCoeff_C_mul_of_isUnit hcu, hc]
  have hsep : (C c * f).Separable ↔ f.Separable := by
    rw [separable_def, separable_def, derivative_C_mul,
      isCoprime_mul_unit_left_left (isUnit_C.mpr hcu),
      isCoprime_mul_unit_left_right (isUnit_C.mpr hcu)]
  rw [← hsep, ← hmonic.isUnit_resultant_derivative_iff, natDegree_C_mul_of_isUnit hcu,
    derivative_C_mul, resultant_C_mul_left, resultant_C_mul_right,
    resultant_deriv (natDegree_pos_iff_degree_pos.mp h0), (hcu.pow _).mul_left_iff,
    (hcu.pow _).mul_left_iff, ((isUnit_one.neg.pow _ : IsUnit ((-1 : R) ^ _)).mul hlc).mul_left_iff]

/-- A monic polynomial has unit discriminant if and only if it is separable. -/
theorem Monic.isUnit_discr_iff (hf : f.Monic) : IsUnit f.discr ↔ f.Separable :=
  isUnit_discr_iff_separable (hf.leadingCoeff ▸ isUnit_one)

end discr

end Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

theorem Monic.resultant_one_right (hg : g.Monic) (n : ℕ) : g.resultant 1 g.natDegree n = 1 := by
  rw [Polynomial.resultant_one_right, hg.coeff_natDegree, one_pow]

/-- The resultant of `f` with the linear polynomial `C x - X` is `f.eval x`.
There is no sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
theorem resultant_C_sub_X (f : R[X]) (x : R) {m : ℕ} (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  rw [← neg_sub, ← neg_one_mul, ← C_1, ← C_neg, resultant_C_mul_right]
  simp [hm, ← mul_assoc, ← mul_pow]

section Sylvester

open Module LinearMap

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-- Multiplication by `p` on `R[X]_(g.natDegree)`, that is, `q ↦ (p * q) %ₘ g`: the map that
`AdjoinRoot.degreeLTEquiv` turns into multiplication by `AdjoinRoot.mk g p`. -/
noncomputable def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext : 1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext : 1; simp [smul_modByMonic]

@[simp]
theorem mulModByMonic_apply_coe (hg : g.Monic) (p : R[X]) (q : degreeLT R g.natDegree) :
    (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  rfl

/-- For monic `g`, the Sylvester map of `g` and `1`, `(u, v) ↦ g * v + u`, as a linear
equivalence `R[X]_(g.natDegree) × R[X]_n ≃ₗ R[X]_(g.natDegree + n)`; its inverse is division
with remainder by `g`. -/
noncomputable def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) where
  __ := sylvesterMap g 1 le_rfl (by simp)
  invFun q := (⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩, ⟨q /ₘ g, divByMonic_mem_degreeLT hg q.2⟩)
  left_inv w := by
    have h := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp [self_mul_add_modByMonic hg, (modByMonic_eq_self_iff hg).mpr h]
    · simp [self_mul_add_divByMonic hg, (divByMonic_eq_zero_iff hg).mpr h]
  right_inv q := Subtype.ext <| by simpa [add_comm] using modByMonic_add_div (q : R[X]) g

@[simp]
theorem coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  rfl

theorem coe_sylvesterEquivOne_symm_apply_fst (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    (((sylvesterEquivOne hg n).symm q).1 : R[X]) = (q : R[X]) %ₘ g :=
  rfl

theorem coe_sylvesterEquivOne_symm_apply_snd (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    (((sylvesterEquivOne hg n).symm q).2 : R[X]) = (q : R[X]) /ₘ g :=
  rfl

/-- The block-triangular endomorphism `Ψ⁻¹ ∘ₗ S` of `R[X]_(g.natDegree) × R[X]_n`, for the
Sylvester map `S` of `g` and `p` and `Ψ = Polynomial.sylvesterEquivOne hg n`. -/
noncomputable def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp

theorem coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe, coe_sylvesterEquivOne_symm_apply_fst,
    sylvesterMap_apply_coe, self_mul_add_modByMonic hg]

theorem coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe, coe_sylvesterEquivOne_symm_apply_snd,
    sylvesterMap_apply_coe, self_mul_add_divByMonic hg]

theorem sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (x : degreeLT R g.natDegree × degreeLT R n) :
    (sylvesterBlock hg p hp x).1 = mulModByMonic hg p x.1 :=
  Subtype.ext <| coe_sylvesterBlock_apply_fst hg p hp x.1 x.2

theorem sylvesterBlock_apply_zero_left (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (v : degreeLT R n) :
    sylvesterBlock hg p hp (0, v) = (0, v) :=
  Prod.ext (Subtype.ext <| by simp [coe_sylvesterBlock_apply_fst])
    (Subtype.ext <| by simp [coe_sylvesterBlock_apply_snd])

theorem sylvesterMap_one_comp_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    sylvesterMap g 1 le_rfl (by simp) ∘ₗ sylvesterBlock hg p hp = sylvesterMap g p le_rfl hp := by
  rw [sylvesterBlock, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg n,
    LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, id_comp]

open Matrix in
/-- The matrix of `Polynomial.sylvesterBlock hg p hp` in the product of the monomial bases is
block lower triangular, with diagonal blocks the matrix of `Polynomial.mulModByMonic hg p` and
`1`. -/
theorem toMatrix_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    toMatrix ((degreeLT.basis R g.natDegree).prod (degreeLT.basis R n))
        ((degreeLT.basis R g.natDegree).prod (degreeLT.basis R n)) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix (degreeLT.basis R g.natDegree) (degreeLT.basis R g.natDegree)
          (mulModByMonic hg p)) 0
        (.of fun i j ↦ (degreeLT.basis R n).repr
          (sylvesterBlock hg p hp (degreeLT.basis R g.natDegree j, 0)).2 i) 1 := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply,
      sylvesterBlock_apply_fst]
  · rw [toMatrix_apply, hinr, sylvesterBlock_apply_zero_left, Basis.prod_repr_inl,
      fromBlocks_apply₁₂]
    simp
  · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
  · rw [toMatrix_apply, hinr, sylvesterBlock_apply_zero_left, Basis.prod_repr_inr,
      fromBlocks_apply₂₂, Basis.repr_self, one_apply, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl

open Matrix in
/-- The determinant of the block-triangular map `Polynomial.sylvesterBlock hg p hp` is the
determinant of its upper-left block `Polynomial.mulModByMonic hg p`. -/
theorem det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  rw [← det_toMatrix ((degreeLT.basis R g.natDegree).prod (degreeLT.basis R n)),
    ← det_toMatrix (degreeLT.basis R g.natDegree), toMatrix_sylvesterBlock,
    det_fromBlocks_zero₁₂, det_one, mul_one]

end Sylvester

/-- `Res(a, b ^ 2 + a * r) = lc(a) ^ (n - 2 deg b) * Res(a, b) ^ 2` in degree `n`, if `n` is at
least `2 deg b` and `deg r + deg a`: the multiple of `a` drops out
(`Polynomial.resultant_add_mul_right`), and the resultant is multiplicative in its second
argument (`Polynomial.resultant_mul_right`). -/
theorem resultant_sq_add_mul_right (a b r : R[X]) {n : ℕ} (hb : 2 * b.natDegree ≤ n)
    (hr : r.natDegree + a.natDegree ≤ n) :
    a.resultant (b ^ 2 + a * r) a.natDegree n =
      a.leadingCoeff ^ (n - 2 * b.natDegree) * a.resultant b ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [resultant_add_mul_right _ _ _ _ _ hr le_rfl, add_tsub_cancel_left,
    resultant_add_right_deg _ _ _ _ _ (natDegree_pow_le_of_le 2 le_rfl), two_mul, sq b,
    resultant_mul_right _ _ _ _ le_rfl, coeff_natDegree, sq]

/-- If `f` is a square modulo `a`, then `lc(a) ^ deg f * Res(a, f)` is a square: over a splitting
field, `Res(a, f)` is `lc(a) ^ deg f` times the product of the values `f(α) = b(α) ^ 2` at the
roots `α` of `a`. The proof computes `Res(a, f)` in a large even excess degree in two ways,
with `Polynomial.resultant_add_right_deg` and `Polynomial.resultant_sq_add_mul_right`. -/
theorem isSquare_leadingCoeff_pow_mul_resultant_of_dvd_sq_sub {K : Type*} [Field K] {a b f : K[X]}
    (h : a ∣ b ^ 2 - f) : IsSquare (a.leadingCoeff ^ f.natDegree * a.resultant f) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0 ^ f.natDegree, by simp⟩
  obtain ⟨q, hq⟩ := h
  set e := q.natDegree + a.natDegree
  have h₁ := resultant_add_right_deg a f a.natDegree f.natDegree (2 * (b.natDegree + e)) le_rfl
  have h₂ := resultant_sq_add_mul_right a b (-q) (n := f.natDegree + 2 * (b.natDegree + e)) (by lia)
    (by lia [natDegree_neg q])
  rw [show b ^ 2 + a * -q = f by linear_combination hq, h₁, coeff_natDegree,
    show f.natDegree + 2 * (b.natDegree + e) - 2 * b.natDegree = f.natDegree + 2 * e by lia] at h₂
  have hl : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha
  refine ⟨a.leadingCoeff ^ (f.natDegree + e) * a.resultant b / a.leadingCoeff ^ (b.natDegree + e),
    ?_⟩
  linear_combination (norm := field)
    a.leadingCoeff ^ f.natDegree * h₂ / a.leadingCoeff ^ (2 * (b.natDegree + e))

/-- The value of `q` at a root of `g` divides the resultant of `g` and `q`: evaluate a Bézout
identity `g a + q b = Res(g, q)` there. -/
theorem eval_dvd_resultant_of_eval_eq_zero {q : R[X]} {θ : R} (hθ : g.eval θ = 0) {m n : ℕ}
    (hm : g.natDegree ≤ m) (hn : q.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0) :
    q.eval θ ∣ g.resultant q m n := by
  obtain ⟨_, b, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant g q hm hn H
  exact ⟨b.eval θ, by simpa [hθ] using congr(eval θ $e).symm⟩

section Map

variable {S : Type*} [CommRing S] {φ : R →+* S}

theorem discr_map_of_injective (hφ : Function.Injective φ) (f : R[X]) :
    (f.map φ).discr = φ f.discr :=
  discr_map φ (natDegree_map_eq_of_injective hφ f)

end Map

/-- Over a domain, a polynomial prime to its derivative (a separable one) has a nonzero
discriminant: by `Polynomial.resultant_deriv`, `lc(f) * disc(f)` is up to sign the resultant of `f`
and `f'` with `f'` of formal degree `deg f - 1`, which is a power of `lc(f)` times their resultant
(`Polynomial.resultant_add_right_deg`) and does not vanish as `f` and `f'` are coprime. -/
theorem discr_ne_zero_of_isCoprime_derivative [IsDomain R] {f : R[X]}
    (hf : IsCoprime f (derivative f)) : f.discr ≠ 0 := by
  rcases le_or_gt f.degree 0 with h | h
  · rw [eq_C_of_degree_le_zero h, discr_C]
    exact one_ne_zero
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (natDegree_derivative_le f)
  have h0 := resultant_deriv h
  rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree] at h0
  exact right_ne_zero_of_mul (h0 ▸ mul_ne_zero
    (pow_ne_zero _ (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h))) (resultant_ne_zero f _ hf))

section

variable {f : R[X]}

/-- For monic `f`, the resultant `Res(f, h)` does not depend on the formal degree of `h`. -/
theorem Monic.resultant_eq_of_natDegree_le (hf : f.Monic) {h : R[X]} {n n' : ℕ}
    (hh : h.natDegree ≤ n) (hn : n ≤ n') :
    resultant f h f.natDegree n' = resultant f h f.natDegree n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg _ _ _ _ k hh, hf.coeff_natDegree, one_pow, one_mul]

theorem Monic.resultant_mul_right (hf : f.Monic) {h₁ h₂ : R[X]} {n₁ n₂ : ℕ}
    (h₁n : h₁.natDegree ≤ n₁) (h₂n : h₂.natDegree ≤ n₂) :
    resultant f (h₁ * h₂) f.natDegree (n₁ + n₂) =
      resultant f h₁ f.natDegree n₁ * resultant f h₂ f.natDegree n₂ := by
  rw [hf.resultant_eq_of_natDegree_le (natDegree_mul_le.trans (add_le_add h₁n h₂n)) le_rfl,
    hf.resultant_eq_of_natDegree_le natDegree_mul_le (add_le_add h₁n h₂n),
    Polynomial.resultant_mul_right _ _ _ _ le_rfl, hf.resultant_eq_of_natDegree_le le_rfl h₁n,
    hf.resultant_eq_of_natDegree_le le_rfl h₂n]

/-- `Res(f, (f g)') = Res(f, f') Res(f, g)` for monic `f` of positive degree, as `f` divides
`f g'`. -/
theorem Monic.resultant_derivative_mul (hf : f.Monic) (hf0 : 0 < f.natDegree)
    (hg0 : 0 < g.natDegree) :
    resultant f (derivative (f * g)) f.natDegree (f.natDegree + g.natDegree - 1) =
      resultant f (derivative f) f.natDegree (f.natDegree - 1) * resultant f g := by
  rw [derivative_mul, resultant_add_mul_right _ _ _ _ _ _ le_rfl, Nat.sub_add_comm hf0,
    hf.resultant_mul_right (natDegree_derivative_le f) le_rfl]
  have := natDegree_derivative_le g
  lia

@[simp]
theorem discr_one : discr (1 : R[X]) = 1 :=
  C_1 (R := R) ▸ discr_C 1

private theorem neg_one_pow_add_mul_sub_one_div_two (m n : ℕ) :
    (-1 : R) ^ ((m + n) * (m + n - 1) / 2) =
      (-1) ^ (m * (m - 1) / 2) * (-1) ^ (n * (n - 1) / 2) * (-1) ^ (m * n) := by
  simp only [← Nat.choose_two_right, Nat.add_choose_two, pow_add]

/-- The **discriminant of a product** of monic polynomials:
`disc (f g) = disc f * disc g * Res(f, g) ^ 2`. -/
theorem Monic.discr_mul (hf : f.Monic) (hg : g.Monic) :
    (f * g).discr = f.discr * g.discr * resultant f g ^ 2 := by
  nontriviality R
  rcases Nat.eq_zero_or_pos f.natDegree with hf0 | hf0
  · simp [hf.natDegree_eq_zero.mp hf0]
  rcases Nat.eq_zero_or_pos g.natDegree with hg0 | hg0
  · simp [hg.natDegree_eq_zero.mp hg0]
  have key := resultant_deriv (f := f * g) (natDegree_pos_iff_degree_pos.mp (by
    rw [hf.natDegree_mul hg]; lia))
  rw [(hf.mul hg).leadingCoeff, hf.natDegree_mul hg, resultant_mul_left _ _ _ _
    ((natDegree_derivative_le _).trans (by rw [hf.natDegree_mul hg])),
    hf.resultant_derivative_mul hf0 hg0, mul_comm f g, add_comm f.natDegree,
    hg.resultant_derivative_mul hg0 hf0, resultant_deriv (natDegree_pos_iff_degree_pos.mp hf0),
    resultant_deriv (natDegree_pos_iff_degree_pos.mp hg0), resultant_comm g f,
    hf.leadingCoeff, hg.leadingCoeff, add_comm g.natDegree,
    neg_one_pow_add_mul_sub_one_div_two, mul_comm g f, mul_comm g.natDegree f.natDegree] at key
  refine (((isUnit_neg_one.pow (f.natDegree * (f.natDegree - 1) / 2)).mul
    (isUnit_neg_one.pow (g.natDegree * (g.natDegree - 1) / 2))).mul
      (isUnit_neg_one.pow (f.natDegree * g.natDegree))).mul_left_cancel ?_
  linear_combination -key

/-- A polynomial over a field with nonzero discriminant is separable, as `Res(f, f')` is
`± lc(f) * disc f` (`Polynomial.resultant_deriv`). -/
theorem separable_of_discr_ne_zero {K : Type*} [Field K] {f : K[X]} (hf : 0 < f.degree)
    (h : f.discr ≠ 0) : f.Separable := by
  by_contra hc
  have h0 := resultant_eq_zero_iff.mpr ⟨.inl (ne_zero_of_degree_gt hf), hc⟩
  have hd := resultant_deriv hf
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (natDegree_derivative_le f)
  rw [hk, resultant_add_right_deg _ _ _ _ _ le_rfl, h0, mul_zero] at hd
  simp [h, ne_zero_of_degree_gt hf] at hd

end

end Polynomial

end
