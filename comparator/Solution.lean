import HyperellipticCurves.Count.Arithmetic
import HyperellipticCurves.Count.NumberField

/-!
# Comparator solutions

Proofs of the three challenge theorems from `Challenge.lean`, discharged by the library
theorems of `HyperellipticCurves/Count/NumberField.lean` and
`HyperellipticCurves/Count/Arithmetic.lean`: `challenge_main_affine_numberField` and
`challenge_ratPoints_finite_numberField` by
`ChabautyColeman.NumberFieldBase.main_affine_numberField` / `ratPoints_finite_numberField` — the
instantiation of the abstract main theorems at the local factor `O` of `W(𝔽̄_p) ⊗ 𝓞 K`, `K₀ = K`,
`O₀` the ring of `v`-integers of `K` — and `challenge_main_affine` by their case `A = ℤ`, `K = ℚ`,
`v = (p)` (`ChabautyColeman.main_affine_rat_of_rank_le`). The library theorems are stated for a
hyperelliptic curve `HyperellipticCurve.ofMonicOdd hf hodd hsep`, whose separability is supplied by
the squarefreeness hypotheses (`ChabautyColeman.separable_of_squarefree_twist`,
`ChabautyColeman.NumberFieldBase.separable_of_squarefree_map_residue`); its genus `f.natDegree / 2`
and its polynomial `f` are the challenge's data definitionally. Every notion in the statements is a
Mathlib definition, so Comparator's body-level comparison of the challenge and solution statements
is over Mathlib definitions only; the challenges' assumed `IsDomain` instances are
interchangeable with the library's `ChabautyColeman.HypRing.instIsDomain` by proof
irrelevance.
-/

open Polynomial IsDedekindDomain

open scoped TensorProduct NumberField

/-- **The Chabauty–Coleman bound over `ℚ`** (blueprint `thm:main`): for a monic `f : ℚ[X]` of
odd degree that is `p`-integral — `d·f = F` with `F : ℤ[X]` and `p ∤ d` — whose reduction
mod the prime `p` is squarefree, if the rank of the rationalized Jacobian
`ℚ ⊗ Cl(ℚ[x][y]/(y² - f))` is at most `r`, where `r` is smaller than the genus
`g = f.natDegree / 2`, and `p > 2r + 2`, then
`#{(x,y) ∈ ℚ² : y² = f(x)} + 1 ≤ #{(x,y) ∈ 𝔽_p² : d̄·y² = F̄(x)} + 1 + 2r`. The reduction
of `f` mod `p` is `d̄⁻¹·F̄`, so the right-hand side counts the points of `y² = f̄(x)`. -/
theorem challenge_main_affine (f : ℚ[X]) (p : ℕ) (hp : p.Prime) (hf : f.Monic)
    (hodd : Odd f.natDegree) (F : ℤ[X]) (d : ℤ) (hd : ¬ (p : ℤ) ∣ d)
    (hF : F.map (Int.castRingHom ℚ) = C (d : ℚ) * f)
    (hsq : Squarefree (F.map (Int.castRingHom (ZMod p))))
    (r : ℕ) (hpr : 2 * r + 2 < p) (hrg : r < f.natDegree / 2)
    -- The coordinate ring `ℚ[x][y]/(y² - f)` of the curve is a domain; this is a theorem
    -- (`ChabautyColeman.HypRing.instIsDomain`), but the `ClassGroup` term below does not
    -- elaborate from Mathlib alone without the instance, so it is taken as a hypothesis.
    [IsDomain (QuadraticAlgebra ℚ[X] f 0)]
    (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive (ClassGroup (QuadraticAlgebra ℚ[X] f 0))) ≤ r) :
    {q : ℚ × ℚ | q.2 ^ 2 = f.eval q.1}.encard + 1
      ≤ ({q : ZMod p × ZMod p
            | (d : ZMod p) * q.2 ^ 2 = (F.map (Int.castRingHom (ZMod p))).eval q.1}.encard + 1)
        + 2 * r := by
  have : Fact p.Prime := ⟨hp⟩
  exact ChabautyColeman.main_affine_rat_of_rank_le
    (.ofMonicOdd hf hodd (ChabautyColeman.separable_of_squarefree_twist hf hd hF hsq)) hd hF hsq
    hpr hrk hrg

/-- **The Chabauty–Coleman bound over a number field** (blueprint `thm:main-nf`; Stoll,
Compositio Math. 142 (2006), Cor. 6.7): for a monic `f : K[X]` of odd degree over a number
field `K` and a prime `v` of `𝓞 K` at which `f` is integral — `f` is the image of `fA` over
the ring of `v`-integers `v.valuationSubringAtPrime K` — with squarefree reduction
`fA mod v`, if the rank of the rationalized Jacobian `ℚ ⊗ Cl(K[x][y]/(y² - f))` is at most
`r`, where `r` is smaller than the genus `g = f.natDegree / 2`, and `p > 2r + e + 1` for the
residue characteristic `p` and the ramification index `e = Ideal.ramificationIdx'
(v.asIdeal.under ℤ) v.asIdeal`, then
`#{(x,y) ∈ K² : y² = f(x)} + 1 ≤ #{(x,y) ∈ 𝔽_v² : y² = f̄(x)} + 1 + 2r`, where `𝔽_v` is the
residue field of the ring of `v`-integers. -/
theorem challenge_main_affine_numberField {K : Type*} [Field K] [NumberField K]
    (f : K[X]) (hf : f.Monic) (hodd : Odd f.natDegree) (v : HeightOneSpectrum (𝓞 K))
    (fA : (v.valuationSubringAtPrime K)[X]) (hfA : fA.map (algebraMap _ K) = f)
    (hsq : Squarefree (fA.map (IsLocalRing.residue _)))
    (r : ℕ) (hpr : 2 * r + Ideal.ramificationIdx' (v.asIdeal.under ℤ) v.asIdeal + 1
      < ringChar (IsLocalRing.ResidueField (v.valuationSubringAtPrime K)))
    (hrg : r < f.natDegree / 2)
    -- The coordinate ring `K[x][y]/(y² - f)` of the curve is a domain; this is a theorem
    -- (`ChabautyColeman.HypRing.instIsDomain`), but the `ClassGroup` term below does not
    -- elaborate from Mathlib alone without the instance, so it is taken as a hypothesis.
    [IsDomain (QuadraticAlgebra K[X] f 0)]
    (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive (ClassGroup (QuadraticAlgebra K[X] f 0))) ≤ r) :
    {q : K × K | q.2 ^ 2 = f.eval q.1}.encard + 1
      ≤ ({q : IsLocalRing.ResidueField (v.valuationSubringAtPrime K)
            × IsLocalRing.ResidueField (v.valuationSubringAtPrime K)
            | q.2 ^ 2 = (fA.map (IsLocalRing.residue _)).eval q.1}.encard + 1)
        + 2 * r := by
  exact ChabautyColeman.NumberFieldBase.main_affine_numberField
    (.ofMonicOdd hf hodd
      (ChabautyColeman.NumberFieldBase.separable_of_squarefree_map_residue hf hodd.pos hfA hsq))
    hfA hsq hpr hrk hrg

/-- **Finiteness of the rational points over a number field** (blueprint
`cor:finiteness-nf`): for a monic squarefree `f : K[X]` of odd degree over a number field
`K`, under the rank hypothesis the affine `K`-solution set of `y² = f(x)` is finite. No
prime appears: a suitable prime of `𝓞 K` exists for every such `f`. At `K = ℚ` this is the
finiteness of the rational solution set of a monic squarefree rational polynomial of odd
degree under the rank hypothesis. -/
theorem challenge_ratPoints_finite_numberField {K : Type*} [Field K] [NumberField K]
    (f : K[X]) (hf : f.Monic) (hodd : Odd f.natDegree) (hsq : Squarefree f)
    -- The coordinate ring `K[x][y]/(y² - f)` of the curve is a domain; this is a theorem
    -- (`ChabautyColeman.HypRing.instIsDomain`), but the `ClassGroup` term below does not
    -- elaborate from Mathlib alone without the instance, so it is taken as a hypothesis.
    [IsDomain (QuadraticAlgebra K[X] f 0)]
    (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive (ClassGroup (QuadraticAlgebra K[X] f 0)))
      < (f.natDegree / 2 : ℕ)) :
    {q : K × K | q.2 ^ 2 = f.eval q.1}.Finite := by
  exact ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField (𝓞 K)
    (.ofMonicOdd hf hodd (PerfectField.separable_iff_squarefree.mpr hsq)) hrk
