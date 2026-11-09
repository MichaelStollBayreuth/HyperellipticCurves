/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Archive.CurveDerivation
public import HyperellipticCurves.Log.Charts.PhiChart

/-!
# The global chart: the disk chart coordinates as functions on the curve

The Cantor pipeline of `def:phiD` run at the **generic point** `P = (x, y)` of the curve,
over the function field `F_K = K(x)[Y]/(Y² - f)`: the same certified three-block addition
`[P + ιQ - 2∞] + τ + [Q + ιP₀ - 2∞] = [P] - [P₀] + τ` as `ChabautyColeman.phiPipeline`,
with the disk parametrization `(a + z, b·η(z))` replaced by the coordinate functions
`(x, y)` (`ChabautyColeman.HypField.x`, `ChabautyColeman.HypField.y`). The resulting
chart coordinates `ChabautyColeman.globZeta` are honest **functions on the curve**; their
disk expansions recover `ChabautyColeman.phiZeta`
(`ChabautyColeman.globExpand_globZeta`), and the global differentials of `thm:omega-prime-global`
clause (c) are `ω′_i = φ_i·dx/y` with `φ_i = y·∑_j N_{ij}(ζ)·D(ζ_j)` for the curve
derivation `D` (`HyperellipticCurves.Archive.CurveDerivation`).

The moving pair datum is the line through `(x, y)` and `ιQ` with the honest slope
`ChabautyColeman.globSlope` — a genuine function-field element, no certificate needed
(`ChabautyColeman.globSlope_spec`); the two pair data are on the curve
(`ChabautyColeman.globPair_dvd`, `ChabautyColeman.globPair₃_dvd`); the three blocks
together form `ChabautyColeman.globConfig`. Following the
certificate-passing convention of `def:Ftau`/`def:phiD`, the reduction certificate pack
`d` over `F_K` is a parameter.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section GenericPoint

variable {K : Type*} [Field K] (f : K[X])

namespace HypField

/-- The coordinate function `x` on the curve, as an element of the function field. -/
noncomputable abbrev x : HypField K f := algebraMap K[X] (HypField K f) X

/-- Evaluating a polynomial (as a function of `x`) at the coordinate function recovers its
image in the function field. -/
theorem aeval_x (p : K[X]) : aeval (x f) p = algebraMap K[X] (HypField K f) p := by
  rw [show x f = (IsScalarTower.toAlgHom K K[X] (HypField K f)) X from rfl,
    aeval_algHom_apply, aeval_X_left_apply]
  rfl

/-- The curve derivation differentiates the coordinate function to `1`: `D(x) = 1`. -/
@[simp] theorem deriv_x : deriv (x f) = 1 := by
  rw [deriv_algebraMap_polynomial, derivative_X, map_one]

/-- The on-curve identity in evaluation form: `y² = f(x)` in the function field. -/
theorem y_sq_eval : y f ^ 2 = (f.map (algebraMap K (HypField K f))).eval (x f) := by
  rw [y_sq, eval_map, ← aeval_def, aeval_x]

theorem algebraMap_polynomial_injective :
    Function.Injective (algebraMap K[X] (HypField K f)) := by
  rw [IsScalarTower.algebraMap_eq K[X] (RatFunc K) (HypField K f)]
  exact (algebraMap (RatFunc K) (HypField K f)).injective.comp (RatFunc.algebraMap_injective K)

/-- The distinguished square root is nonzero unless the curve is: `y² = f`. -/
theorem y_ne_zero (hf0 : f ≠ 0) : y f ≠ 0 := fun h ↦
  hf0 (algebraMap_polynomial_injective f (((y_sq f).symm.trans (by
    rw [h]; ring)).trans
    (map_zero _).symm))

/-- The coordinate function is transcendental over the constants: `x ≠ c` for `c ∈ K`. -/
theorem algebraMap_sub_x_ne_zero (c : K) : algebraMap K (HypField K f) c - x f ≠ 0 := by
  intro h
  have hinj := algebraMap_polynomial_injective f
  have hCc : algebraMap K (HypField K f) c = algebraMap K[X] (HypField K f) (C c) := by
    rw [IsScalarTower.algebraMap_apply K K[X] (HypField K f), algebraMap_eq]
  rw [hCc, x, ← map_sub] at h
  have := hinj (h.trans (map_zero _).symm)
  exact X_ne_C c (by linear_combination -this)

end HypField

open HypField

variable [Fact (Odd f.natDegree)]

/-- The slope of the line through the generic point `(x, y)` and `ιQ = (x_Q, -y_Q)`, as a
function-field element. -/
noncomputable def globSlope (xQ yQ : K) : HypField K f :=
  (algebraMap K (HypField K f) (-yQ) - y f) / (algebraMap K (HypField K f) xQ - x f)

/-- The slope certificate identity for `globSlope` (the global analogue of the per-disk
slope certificate `hm` of `def:phiD`). -/
theorem globSlope_spec (xQ yQ : K) :
    globSlope f xQ yQ * (algebraMap K (HypField K f) xQ - x f)
      = algebraMap K (HypField K f) (-yQ) - y f :=
  div_mul_cancel₀ _ (algebraMap_sub_x_ne_zero f xQ)

/-- The `u`-polynomial of the global moving pair datum: the divisor `(P) + (ιQ)` with `P`
the generic point. -/
noncomputable def globU₁ (xQ : K) : (HypField K f)[X] :=
  (X - C (x f)) * (X - C (algebraMap K (HypField K f) xQ))

/-- The `v`-polynomial of the global moving pair datum: the line through `(x, y)` and
`(x_Q, -y_Q)`. -/
noncomputable def globV₁ (xQ yQ : K) : (HypField K f)[X] :=
  pairV (x f) (y f) (globSlope f xQ yQ)

/-- The global moving pair is on the curve: `u₁ ∣ v₁² - f`. -/
theorem globPair_dvd {xQ yQ : K} (hyQ : yQ ^ 2 = f.eval xQ) :
    globU₁ f xQ ∣ globV₁ f xQ yQ ^ 2 - f.map (algebraMap K (HypField K f)) := by
  refine pair_dvd (isUnit_iff_ne_zero.mpr (algebraMap_sub_x_ne_zero f xQ))
    (globSlope_spec f xQ yQ) (y_sq_eval f) ?_
  rw [eval_map, Polynomial.eval₂_at_apply]
  rw [show algebraMap K (HypField K f) (-yQ) = -(algebraMap K (HypField K f) yQ) from
    map_neg _ yQ, neg_pow, ← map_pow, hyQ]
  norm_num

/-- The `u`-polynomial of the global constant pair datum: the divisor `(Q) + (ιP₀)` with
`P₀ = (a, b)` the disk center. -/
noncomputable def globU₃ (a xQ : K) : (HypField K f)[X] :=
  ((X - C xQ) * (X - C a)).map (algebraMap K (HypField K f))

/-- The `v`-polynomial of the global constant pair datum (slope certificate `m₀`). -/
noncomputable def globV₃ (xQ yQ m₀ : K) : (HypField K f)[X] :=
  (pairV xQ yQ m₀).map (algebraMap K (HypField K f))

/-- The global constant pair is on the curve. -/
theorem globPair₃_dvd {a b xQ yQ m₀ : K} (hsep' : a ≠ xQ) (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hyQ : yQ ^ 2 = f.eval xQ) :
    globU₃ f a xQ ∣ globV₃ f xQ yQ m₀ ^ 2 - f.map (algebraMap K (HypField K f)) := by
  have h := pair_dvd (F := f) (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hsep')) hm₀ hyQ
    (by rw [neg_pow]; norm_num; exact hb)
  have hmap := map_dvd (mapRingHom (algebraMap K (HypField K f))) h
  simpa only [coe_mapRingHom, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
    globU₃, globV₃] using hmap

/-- **The global three-block configuration is a Mumford configuration**: the six monicity
and curve-divisibility facts for the moving pair `[P + ιQ]`, the `τ`-block and the constant
pair `[Q + ιP₀]` with centre `(a, b)`. -/
theorem globConfig_monic_dvd {a b xQ yQ m₀ : K} (hsep : a ≠ xQ)
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hb : b ^ 2 = f.eval a) (hyQ : yQ ^ 2 = f.eval xQ)
    {u v : K[X]} (hu : u.Monic) (hd : u ∣ v ^ 2 - f) :
    (globU₁ f xQ).Monic ∧ (u.map (algebraMap K (HypField K f))).Monic
      ∧ (globU₃ f a xQ).Monic
      ∧ globU₁ f xQ ∣ globV₁ f xQ yQ ^ 2 - f.map (algebraMap K (HypField K f))
      ∧ u.map (algebraMap K (HypField K f))
          ∣ (v.map (algebraMap K (HypField K f))) ^ 2 - f.map (algebraMap K (HypField K f))
      ∧ globU₃ f a xQ ∣ globV₃ f xQ yQ m₀ ^ 2 - f.map (algebraMap K (HypField K f)) :=
  ⟨(monic_X_sub_C _).mul (monic_X_sub_C _), hu.map _,
    ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _, globPair_dvd f hyQ,
    map_dvd_sq_sub _ hd, globPair₃_dvd f hsep hm₀ hb hyQ⟩

variable (uτ vτ : K[X]) (a xQ yQ m₀ : K) (d : CantorCertData (HypField K f))

/-- **The global three-block configuration**: the moving pair block `[P + ιQ]` at the
generic point, the `τ`-block and the constant pair block `[Q + ιP₀]` at the centre `a` —
all over the function field. The global analogue of `ChabautyColeman.phiConfig`. -/
@[simps] noncomputable def globConfig : PipelineData (HypField K f) :=
  ⟨globU₁ f xQ, globV₁ f xQ yQ, uτ.map (algebraMap K (HypField K f)),
    vτ.map (algebraMap K (HypField K f)), globU₃ f a xQ, globV₃ f xQ yQ m₀⟩

/-- **The global chart pipeline**: the Cantor pipeline computing
`[P + ιQ - 2∞] + τ + [Q + ιP₀ - 2∞] = [P] - [P₀] + τ` at the generic point `P = (x, y)`
of the curve, over the function field, steered by the certificate pack `d`. The global
analogue of `ChabautyColeman.phiPipeline` (same shape, same addition-chain order). -/
noncomputable def globPipeline : (HypField K f)[X] × (HypField K f)[X] :=
  cantorPipeline (f.map (algebraMap K (HypField K f))) (globConfig f uτ vτ a xQ yQ m₀) d

/-- **The global chart coordinates `ζ` as functions on the curve**: the coefficients of the
perturbation of the global pipeline's `u`-part relative to the `τ`-center. The global
analogue of `ChabautyColeman.phiZeta`; the differentials of `thm:omega-prime-global` are
`ω′_i = φ_i·dx/y` with `φ_i = y·∑_j N_{ij}(ζ)·D(ζ_j)`. -/
noncomputable def globZeta (j : Fin uτ.natDegree) : HypField K f :=
  chartCoords (algebraMap K (HypField K f)) uτ (globPipeline f uτ vτ a xQ yQ m₀ d).1 j

end GenericPoint

section GlobalOmega

open HypField

variable {K : Type*} [Field K] (f : K[X]) [Fact (Odd f.natDegree)]
  (uτ vτ : K[X]) (a xQ yQ m₀ : K) (d : CantorCertData (HypField K f))

/-- The global pipeline returns a reduced datum: `(globPipeline).1` is monic, divides
`(globPipeline).2 ^ 2 - f`, and dominates `(globPipeline).2` in degree. The global analogue
of `ChabautyColeman.phiPipeline_monic_dvd_degree_lt`. -/
theorem globPipeline_monic_dvd_degree_lt {b : K} (hsep' : a ≠ xQ)
    (hm₀ : m₀ * (a - xQ) = -b - yQ) (hb : b ^ 2 = f.eval a) (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hcerts : IsPipelineCerts (f.map (algebraMap K (HypField K f))) (globConfig f uτ vτ a xQ yQ m₀)
      d
      uτ.natDegree) :
    (globPipeline f uτ vτ a xQ yQ m₀ d).1.Monic
      ∧ (globPipeline f uτ vτ a xQ yQ m₀ d).1
        ∣ (globPipeline f uτ vτ a xQ yQ m₀ d).2 ^ 2 - f.map (algebraMap K (HypField K f))
      ∧ (globPipeline f uτ vτ a xQ yQ m₀ d).2.degree
        < (globPipeline f uτ vτ a xQ yQ m₀ d).1.degree := by
  have hu₁ : (globU₁ f xQ).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂ : (uτ.map (algebraMap K (HypField K f))).Monic := huτ.map _
  have hu₃ : (globU₃ f a xQ).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  exact cantorPipeline_monic_dvd_degree_lt hu₁ (globPair_dvd f hyQ) hu₂
    (map_dvd_sq_sub _ hdvdτ) hu₃ (globPair₃_dvd f hsep' hm₀ hb hyQ) hcerts

/-- The `u`-part of the global pipeline is the `τ`-center perturbed by the global chart
coordinates: `U = uτ + ∑ ζ_j·X^j`. The global analogue of the `phiZeta` decomposition. -/
theorem globPipeline_fst_eq_add_globZeta (huτ : uτ.Monic)
    (hmonic : (globPipeline f uτ vτ a xQ yQ m₀ d).1.Monic)
    (hdeg : (globPipeline f uτ vτ a xQ yQ m₀ d).1.natDegree = uτ.natDegree) :
    (globPipeline f uτ vτ a xQ yQ m₀ d).1
      = uτ.map (algebraMap K (HypField K f))
        + ∑ j : Fin uτ.natDegree, C (globZeta f uτ vτ a xQ yQ m₀ d j) * X ^ (j : ℕ) :=
  eq_add_chartCoords (algebraMap K (HypField K f)) huτ hmonic hdeg

/-- **The global differential numerator `φ_i`** (`thm:omega-prime-global` clause (c)): the
function `φ_i = y·∑_j N_{ij}·D(ζ_j)` on the curve, so that `ω′_i = φ_i·dx/y`. Following
the certificate-passing convention, the matrix `N` — the inverse differential matrix
`M⁻¹` of `F_τ` evaluated at the chart coordinates `ζ`, which is a rational expression in
the chart data by `ChabautyColeman.invariantDiffFold_rational` — is a *parameter*; its defining
property enters through the disk-expansion identification
(`ChabautyColeman.globExpand_globOmega`). -/
noncomputable def globOmega (N : Fin uτ.natDegree → Fin uτ.natDegree → HypField K f)
    (i : Fin uτ.natDegree) : HypField K f :=
  y f * ∑ j, N i j * HypField.deriv (globZeta f uτ vτ a xQ yQ m₀ d j)

end GlobalOmega

end ChabautyColeman

end
