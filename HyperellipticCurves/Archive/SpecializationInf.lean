/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.FuncExpansionInf
public import HyperellipticCurves.Archive.SpecializationGeneric
public import HyperellipticCurves.Curve.InftyPlace
public import HyperellipticCurves.Disks.OrdMatchIntrinsic

import HyperellipticCurves.Mathlib.Algebra.Polynomial.Div

/-!
# Specialization of a principal divisor (chart form, infinity chart)

The chart-form `thm:spec` strand, on which the main theorems do not depend: the reduction map
is valued in the affine class group, so the specialization theorem they use is the affine
point-sum form (`HyperellipticCurves.Specialization.DiskPointSum` →
`HyperellipticCurves.Specialization.Pointwise`).

The infinity-chart case of the specialization theorem. On the infinity residue disk a function
`h = P + Q·y` has a pole; the expansion is cleared by the monomial `uᴺ·z`
(`ChabautyColeman.funcExpansionInf`), contributing a spurious zero of order `2N+1` at the point
`z = 0`. Subtracting it recovers the intrinsic order at `∞`:

`(#{C_p-zeros of the cleared expansion}) = 2N + 1 + ord_∞(h̄)`,

where `ord_∞(h̄) = inftyOrd(P̄ + Q̄·y) = -deg(P̄² - f̄·Q̄²)`
(`ChabautyColeman.inftyOrd_toHypField`) is the (negative) order of the pole at the infinite
place. This is `thm:spec` at `P̄ = ∞`: the total `C_p`-multiplicity of the zeros reducing to `∞`,
normalized by the clearing monomial, equals the intrinsic order there.

The analytic `C_p` zero-count comes from `ChabautyColeman.zeros_eq_ord`; the individual reduced
order from `ChabautyColeman.order_map_funcExpansionInf` (via evenness of
`ChabautyColeman.infSeries`); the identification of `rootMult₀ (reflect (2N) N̄)` with
`2N - deg N̄` from `Polynomial.rootMultiplicity_zero_reflect`.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

variable {O O' F : Type*} [CommRing O] [IsLocalRing O] [CommRing O'] [Nontrivial O']
  [Field F] [Algebra O' F] [IsFractionRing O' F] [IsAlgClosed F]

/-- **Specialization of a principal divisor (infinity chart, `thm:spec`).** The total
`C_p`-multiplicity of the zeros of the cleared infinity-disk expansion of `P + Q·y`, over an
algebraically closed complete field `F` (the roots of the Weierstrass factor `W`), equals
`2N + 1 + ord_∞(h̄)`: the clearing monomial `uᴺ·z` contributes `2N+1`, and `ord_∞(h̄) =
inftyOrd(P̄ + Q̄·y)` is the intrinsic (negative) order at the infinite place of the reduction. -/
theorem divisor_specialization_inf (φ : O →+* O') {f P Q : O[X]} (hf : f.Monic)
    (hodd : Odd f.natDegree) [Fact (Odd (f.map (residue O)).natDegree)]
    (N : ℕ) (hP : P.natDegree ≤ N) (hQ : Q.natDegree + genus f + 1 ≤ N)
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    {W : O[X]} {u : O⟦X⟧}
    (hfac : (funcExpansionInf P Q hf N).IsWeierstrassFactorization W u) :
    ((∑ᶠ z : F, rootMultiplicity z ((W.map φ).map (algebraMap O' F)) : ℕ) : ℤ)
      = 2 * N + 1 + inftyOrd (HypRing.toHypField (f.map (residue O))
          ⟨P.map (residue O), Q.map (residue O)⟩) := by
  have hnorm : (P.map (residue O)) ^ 2 - (f.map (residue O)) * (Q.map (residue O)) ^ 2
      = (P ^ 2 - f * Q ^ 2).map (residue O) :=
    map_norm_poly (residue O) f P Q
  have hNr : reflect (2 * N) ((P ^ 2 - f * Q ^ 2).map (residue O)) ≠ 0 :=
    reflect_eq_zero_iff.not.mpr hN
  have hdeg : (P ^ 2 - f * Q ^ 2).natDegree ≤ 2 * N := by
    have hdf : f.natDegree = 2 * genus f + 1 := (two_mul_genus_add_one hodd).symm
    refine (natDegree_sub_le _ _).trans (max_le (natDegree_pow_le.trans (by lia)) ?_)
    exact natDegree_mul_le.trans (by have := natDegree_pow_le (p := Q) (n := 2); lia)
  have hdegr : ((P ^ 2 - f * Q ^ 2).map (residue O)).natDegree ≤ 2 * N :=
    natDegree_map_le.trans hdeg
  rw [zeros_eq_ord φ hfac, order_map_funcExpansionInf P Q hf hodd N hP hQ hNr,
    rootMultiplicity_zero_reflect hN hdegr, inftyOrd_toHypField, hnorm,
    show ((1 : ℕ∞) + ↑(2 * N - ((P ^ 2 - f * Q ^ 2).map (residue O)).natDegree)).toNat
      = 1 + (2 * N - ((P ^ 2 - f * Q ^ 2).map (residue O)).natDegree) from by
        rw [← Nat.cast_one, ← Nat.cast_add, ENat.toNat_natCast]]
  lia

end ChabautyColeman
