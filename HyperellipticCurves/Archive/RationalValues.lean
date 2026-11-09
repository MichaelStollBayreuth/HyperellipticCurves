/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Log.Analytic.Lam
public import HyperellipticCurves.Series.FractionTopology

/-!
# Rationality of the values of `λ` (blueprint `lem:values-rational`)

The main theorems do not depend on this file: the annihilator argument runs with pairing
values in the (arbitrary, characteristic-zero) fraction field of the big base, so
`K₀`-valuedness of the pairing is redundant for the count. It is of independent interest (a
Mordell–Weil sieve or effective Coleman extension would want it first).

`ChabautyColeman.lambdaOne_rational_values` is the Galois descent for the pairing
`λ_ω = ∑ᵢ csᵢ·Λᵢ` of `def:lambda1`: its value on a Galois-fixed kernel class is fixed by a
continuous field automorphism `φK` of `K = Frac O` (at the intended instantiation, the
Frobenius of `ℚ_q/ℚ_p`; a fixed value is then a `ℚ_p`-rational value).

Following the blueprint proof, `λ_ω(c)` is characterized τ-freely by clause (b) of
`thm:omega-prime-global` together with additivity: the class decomposes as a finite product
`c = ∏ₜ cdₜ` of same-disk differences (the chart splits every kernel class into `g` disk
differences at the `τ`-support disks), and on each `cdₜ` the value is a convergent power
series `∑ₖ Aₜ(k)·zₜᵏ` — the Coleman integral `∫ ω` over the disk, whose data `(Aₜ, zₜ)`
depend only on `ω` and the disk, not on `τ`. These two facts enter as *hypotheses*
(certificate-passing), together with the Galois symmetry of the characterization: `φK`
permutes the disks by some `σ` and transports the series data accordingly (`ω` being
rational, its expansion at a conjugate disk is the conjugate series). The lemma proves the
genuinely analytic content: since `φK` is continuous (an isometry,
`ChabautyColeman.FractionTopology.continuous_ringEquiv`), applying it to the convergent
characterization of `λ(cdₜ)` yields the characterization of `λ(cd_{σ t})`, so by uniqueness
of limits `φK (λ(cdₜ)) = λ(cd_{σ t})`; summing over the `σ`-permuted family leaves the total
value fixed.

This file is the formalization of blueprint `lem:values-rational`; the assembled
`thm:main-count` takes the `K₀`-rationality of the relevant coordinates as hypotheses instead
and does not reference it.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section RationalValues

universe u'

open ChabautyColeman.FractionTopology

variable {O : Type u'} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {π : O} {p e : ℕ}

/-- **Rationality of the values of `λ`** (blueprint `lem:values-rational`), as Galois
descent: the value of `λ = ∑ᵢ csᵢ·Λᵢ` on a kernel class `c` is fixed by a continuous field
automorphism `φK` of `K = Frac O` (rationality over the fixed field; continuity is supplied
by `ChabautyColeman.FractionTopology.continuous_ringEquiv`), given the τ-free
characterization of the value by `thm:omega-prime-global`(b) and additivity: `c = ∏ₜ cdₜ`
is a finite product of disk differences (`hc`), on each of which the value of `λ` is a
convergent series `∑ₖ Aₜ(k)·zₜᵏ` — the Coleman integral of `ω` over the disk (`hsum`) —
and `φK` permutes the family of series characterizations by `σ` (`hA`, `hz`: `ω` and `c`
are rational, so the conjugate of the disk data at `t` is the disk data at `σ t`). -/
theorem lambdaOne_rational_values
    (φK : FractionRing O ≃+* FractionRing O) (hcont : Continuous φK)
    (cs : Fin n → FractionRing O) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
    (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
    (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
    (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    {ι : Type*} [Fintype ι]
    (cd : ι → (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) (σ : Equiv.Perm ι)
    (z : ι → FractionRing O) (A : ι → ℕ → FractionRing O)
    {c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker} (hc : c = ∏ t, cd t)
    (hsum : ∀ t, HasSum (fun k ↦ A t k * z t ^ k)
      (lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe (cd t)))
    (hA : ∀ t k, φK (A t k) = A (σ t) k) (hz : ∀ t, φK (z t) = z (σ t)) :
    φK (lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram
      hpe c)
      = lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe c := by
  -- the value on each disk difference transports to the conjugate disk difference
  have key t : φK (lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe (cd t))
      = lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe (cd (σ t)) := by
    have h1 := (hsum t).map φK hcont
    have h2 : ⇑φK ∘ (fun k ↦ A t k * z t ^ k) = fun k ↦ A (σ t) k * z (σ t) ^ k := by
      funext k
      simp only [Function.comp_apply, map_mul, map_pow, hA, hz]
    rw [h2] at h1
    exact h1.unique (hsum (σ t))
  -- additivity + reindexing along the permutation
  rw [hc, lambdaOne_prod hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe Finset.univ cd,
    map_sum]
  simp_rw [key]
  exact Equiv.sum_comp σ
    fun t ↦ lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe (cd t)

end RationalValues

end ChabautyColeman

end
