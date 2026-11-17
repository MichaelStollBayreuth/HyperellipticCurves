/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.AuxIndep
public import HyperellipticCurves.Archive.BaseChangeContraction
public import HyperellipticCurves.Archive.BaseChangeEmult
public import HyperellipticCurves.Archive.BaseChangeInjectivity
public import HyperellipticCurves.Archive.CanonDegExact
public import HyperellipticCurves.Archive.ConjugateIdealNorm
public import HyperellipticCurves.Archive.ContentGenerator
public import HyperellipticCurves.Archive.CurveDerivation
public import HyperellipticCurves.Archive.DiskExpand
public import HyperellipticCurves.Archive.Equivariance
public import HyperellipticCurves.Archive.ExpConverge
public import HyperellipticCurves.Archive.ExpInj
public import HyperellipticCurves.Archive.FoldRational
public import HyperellipticCurves.Archive.FormalGroupExp
public import HyperellipticCurves.Archive.FormalGroupPoints
public import HyperellipticCurves.Archive.FuncExpansionInf
public import HyperellipticCurves.Archive.GaloisAction
public import HyperellipticCurves.Archive.GlobalChart
public import HyperellipticCurves.Archive.GlobalDiff
public import HyperellipticCurves.Archive.HenselSmooth
public import HyperellipticCurves.Archive.InftyExpand
public import HyperellipticCurves.Archive.InftyTransport
public import HyperellipticCurves.Archive.J1FiniteIndex
public import HyperellipticCurves.Archive.LogInjective
public import HyperellipticCurves.Archive.Mathlib.Algebra.Polynomial.Degree.Operations
public import HyperellipticCurves.Archive.Mathlib.Algebra.QuadraticAlgebra.Basic
public import HyperellipticCurves.Archive.Mathlib.Algebra.QuadraticAlgebra.Defs
public import HyperellipticCurves.Archive.Mathlib.Algebra.Squarefree.Basic
public import HyperellipticCurves.Archive.Mathlib.FieldTheory.IsAlgClosed.Basic
public import HyperellipticCurves.Archive.Mathlib.FieldTheory.RatFunc.Degree
public import HyperellipticCurves.Archive.Mathlib.RingTheory.MvPowerSeries.CompositionalInverse
public import HyperellipticCurves.Archive.Mathlib.RingTheory.PowerSeries.Basic
public import HyperellipticCurves.Archive.Mathlib.RingTheory.PowerSeries.Order
public import HyperellipticCurves.Archive.OmegaRegular
public import HyperellipticCurves.Archive.RatFuncDerivative
public import HyperellipticCurves.Archive.RationalValues
public import HyperellipticCurves.Archive.RegularDiff
public import HyperellipticCurves.Archive.SecondKind
public import HyperellipticCurves.Archive.SpecializationGeneric
public import HyperellipticCurves.Archive.SpecializationInf
public import HyperellipticCurves.Archive.StableSplitting
public import HyperellipticCurves.Archive.TraceDiskGlobal
public import HyperellipticCurves.Archive.WeierstrassEven
public import HyperellipticCurves.Archive.WeierstrassTransport

/-!
# Archive

Material that is formalized and builds with the project, but on which the main theorems do not
depend. Some blueprint nodes are realized only here.

* **Base-change injectivity of the Jacobian**: for arbitrary field extensions by comparing reduced
  Mumford representatives (`ChabautyColeman.hypJac_map_injective`, in
  `HyperellipticCurves.Archive.BaseChangeInjectivity`), and the finite-Galois (Hilbert-90) route
  for finite Galois extensions (`HyperellipticCurves.Archive.BaseChangeContraction`,
  `HyperellipticCurves.Archive.GaloisAction`). The main theorems use only the base-change
  homomorphism.
* The **place-by-place holomorphy verification** for `thm:omega-prime-global` clause (c): the
  infinite-place expansion of the function field (`HyperellipticCurves.Archive.InftyTransport`),
  the classification of differentials of the second kind
  (`HyperellipticCurves.Archive.SecondKind`), which turns holomorphy into a polynomial numerator,
  and its assembly `ChabautyColeman.omegaPrime_regular` together with the place-by-place
  valuation bounds (`HyperellipticCurves.Archive.OmegaRegular`). The main development uses the
  trace-form identity instead, which exhibits the regular numerator outright rather than
  deducing its existence from holomorphy. The residue disk at `∞` that chapter 4 works with is
  parametrized independently over the base ring in `HyperellipticCurves.Disks.ChartsInf`.
* The **trace-form identity over the function field**: the Cantor pipeline at the generic point
  of the curve, whose chart coordinates are functions on the curve
  (`HyperellipticCurves.Archive.GlobalChart`, with the curve derivation
  `HyperellipticCurves.Archive.CurveDerivation` and the derivative of rational functions
  `HyperellipticCurves.Archive.RatFuncDerivative`), the global inverse differential matrix
  (`HyperellipticCurves.Archive.GlobalDiff`, built on the rationality of the differential matrix
  at the fold, `HyperellipticCurves.Archive.FoldRational`), the expansion homomorphisms
  `F_K →+* Frac(K⟦z⟧)` at a generic, an infinity and a Weierstrass centre
  (`HyperellipticCurves.Archive.DiskExpand`, `HyperellipticCurves.Archive.InftyExpand`,
  `HyperellipticCurves.Archive.WeierstrassTransport`), and the transport of the global trace
  matrix to a disk (`HyperellipticCurves.Archive.TraceDiskGlobal`). The main development runs the
  trace-form identity on each residue disk directly over `Frac(K⟦z⟧)`
  (`HyperellipticCurves.Log.Trace.TraceKz`), with no function field and no expansion
  homomorphisms.
* The **injectivity half of `thm:log-iso`** and everything that serves only to prove it:
  the formal exponential with the inverse identities
  (`HyperellipticCurves.Archive.FormalGroupExp`), its convergence on `(pO)ⁿ`
  (`HyperellipticCurves.Archive.ExpConverge`), the injectivity of the formal and abelian
  logarithms (`HyperellipticCurves.Archive.LogInjective`), and the commutative monoid of
  `𝔪`-points of a formal group law (`HyperellipticCurves.Archive.FormalGroupPoints`). The count
  uses the logarithm only as a homomorphism with integral `π`-scaled coefficients;
  independence/basis arguments run through the trace matrix.
* The **multivariate smooth-point Hensel lemma** (`HyperellipticCurves.Archive.HenselSmooth`):
  every chart root in the main development is a single univariate Hensel root
  (`HyperellipticCurves.Series.HenselRoot`, the realization of `thm:hensel`), so the
  multivariate Newton machinery is not needed. It is a Mathlib gap in its own right.
* The **chart-form `thm:spec` strand**: the `ℂ_p` divisor-specialization statement at every
  point *including* `∞̄` (`HyperellipticCurves.Archive.SpecializationGeneric` /
  `HyperellipticCurves.Archive.SpecializationInf`, with supports
  `HyperellipticCurves.Archive.WeierstrassEven`, `HyperellipticCurves.Archive.FuncExpansionInf`)
  — the reduction map lives in the affine class group and consumes only the point-sum form.
  Alongside: the function-level primitive generator of `lem:content`
  (`HyperellipticCurves.Archive.ContentGenerator`) and the exact canonical degree `2g-2` of
  `lem:canon-deg` (`HyperellipticCurves.Archive.CanonDegExact`).
* Two **Curve-chapter satellites**: the general conjugate-ideal norm identity
  `𝔞·ι(𝔞) = (Nm 𝔞)` (`HyperellipticCurves.Archive.ConjugateIdealNorm` — the main development
  inverts only classes of Mumford ideals, which
  `ChabautyColeman.classGroup_mk0_mumfordIdeal_map_star` does directly), and base-change
  stability of intrinsic multiplicities (`HyperellipticCurves.Archive.BaseChangeEmult`).
* Four **`thm:omega-prime-global` satellites** on which the count does not depend: clause (a),
  auxiliary-point independence (`HyperellipticCurves.Archive.AuxIndep`); the basis half of clause
  (c) (`HyperellipticCurves.Archive.RegularDiff`); expansion injectivity of rational differentials
  (`HyperellipticCurves.Archive.ExpInj`, `lem:exp-inj`); and `K₀`-rationality of the pairing
  values (`HyperellipticCurves.Archive.RationalValues`, `lem:values-rational`).
* The **finite-index theorem for `J¹`** (`thm:J1-index`) and its Frobenius-equivariance
  machinery: the pairing `λ` is defined on `J¹` directly, so no extension to the whole
  Jacobian — and hence no index — is needed. The theorem `ChabautyColeman.J1_finiteIndex`
  with its satellites `ChabautyColeman.redJ_fixed`/`ChabautyColeman.congr_mapBase` lives in
  `HyperellipticCurves.Archive.J1FiniteIndex` (including `lem:frobfix-finite`,
  `ChabautyColeman.frobFixed_finite`); the equivariance of the reduction of ideals under a
  compatible automorphism pack is `HyperellipticCurves.Archive.Equivariance`, and the stability
  of a splitting field under a compatible automorphism is
  `HyperellipticCurves.Archive.StableSplitting`.

Under `HyperellipticCurves.Archive.Mathlib`, a tree mirroring Mathlib's file structure, sits the
general-purpose material that only the Archive depends on, so that `HyperellipticCurves.Mathlib`
contains exactly what the main results need: compositional inverses of multivariate formal
substitutions (`MvPowerSeries.invSubst`), the implication `n² ∣ f·b²` with `f` squarefree ⟹
`n ∣ b` (`Squarefree.dvd_of_sq_dvd_mul_sq`), the degree-bound predicate `RatFunc.IntDegreeLE`,
the ring-homomorphism form of the universal property of a quadratic algebra
(`QuadraticAlgebra.liftRingHom`) together with componentwise sums (`QuadraticAlgebra.re_sum`,
`QuadraticAlgebra.im_sum`), `PowerSeries.rescale` against the base ring
(`ChabautyColeman.rescale_aeval`, `ChabautyColeman.order_rescale_of_isUnit`), and two polynomial
facts (`Polynomial.finite_setOf_natDegree_le_of_coeff_mem`,
`ChabautyColeman.finsum_rootMultiplicity`). Every one of them is a Mathlib gap in its own right.
-/
