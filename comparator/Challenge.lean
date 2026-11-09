import Mathlib

/-!
# Comparator challenge statements

Self-contained restatements of this repository's headline results, with `sorry` proofs,
for verification with [leanprover/comparator](https://github.com/leanprover/comparator):

* the **Chabauty–Coleman bound over `ℚ`** (blueprint `thm:main`,
  `ChabautyColeman.main_affine_rat_of_rank_le` in `HyperellipticCurves/Count/Arithmetic.lean`): for
  a monic `f : ℚ[X]` of odd degree with `p`-integral coefficients — `d·f = F ∈ ℤ[X]` with
  `p ∤ d` — whose reduction mod the prime `p` is squarefree, under the rank hypothesis
  `rk J(ℚ) ≤ r` with `r < genus` and the prime condition `p > 2r + 2`, the number of
  rational points of the hyperelliptic curve `y² = f(x)` is at most the number of points
  of the reduced model `d·y² = F(x)` over `𝔽_p`, plus `2r`;
* the **bound over a number field** (blueprint `thm:main-nf`,
  `ChabautyColeman.NumberFieldBase.main_affine_numberField` in
  `HyperellipticCurves/Count/NumberField.lean`; Stoll, Compositio Math. 142 (2006), Cor. 6.7): the
  same bound over a number field `K` at a prime `v` of `𝓞 K` at which `f ∈ K[x]` is
  integral, with the count over the residue field of `v` and the prime condition
  `p > 2r + e + 1` for the residue characteristic `p` and the ramification index `e`;
* its corollary, **finiteness of the rational points** (blueprint `cor:finiteness-nf`,
  `ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField`) — here no prime appears
  at all: `f ∈ K[x]` monic, squarefree and of odd degree, and the rank hypothesis,
  suffice. At `K = ℚ` this is the finiteness of the rational solution set.

This file imports **only Mathlib**, and the statements involve nothing beyond a polynomial
over `ℚ` resp. over a number field `K`, a prime number `p` resp. a prime `v` of `𝓞 K`, and
an integral model of the polynomial at that prime. Every notion is a Mathlib definition:

* the coordinate ring of the curve is `QuadraticAlgebra K[X] f 0` (`K[x][y]/(y² - f)`);
* its Jacobian is Mathlib's `ClassGroup` of that ring, and the rank hypothesis says that
  the rank of the `ℚ`-vector space `ℚ ⊗[ℤ] Cl(K[x][y]/(y² - f))` is at most a natural
  number `r` smaller than the genus `f.natDegree / 2` (no finite generation is assumed —
  the rank is a cardinal), which for the finiteness statement is weakened to the plain
  inequality `rank < genus`;
* over `ℚ`, `p`-integrality of `f` is certified by `F : ℤ[X]` and `d : ℤ` with `p ∤ d` and
  `F = d·f`, and the reduction is read off `F` and `d` in `ZMod p`;
* over `K`, the prime is a point `v` of the height-one spectrum of `𝓞 K` (a finite place
  of `K`), the ring of `v`-integers of `K` is Mathlib's `v.valuationSubringAtPrime K`,
  integrality of `f` at `v` is certified by a polynomial `fA` over that ring mapping to
  `f`, and the reduction of `f` is the image of `fA` in the residue field of that ring; the
  residue characteristic is the characteristic of that residue field, and the ramification
  index is `Ideal.ramificationIdx' (v.asIdeal.under ℤ) v.asIdeal`;
* the point counts are `Set.encard` of the affine solution sets in `K × K` and in the
  square of the residue field, plus `1` for the point at infinity on each side.

One instance argument is carried as a hypothesis: that the coordinate ring is a domain.
In the library this is a *theorem* (`ChabautyColeman.HypRing.instIsDomain`, from the odd
degree), but the `ClassGroup` term does not elaborate from Mathlib alone without it.

There is no lower bound on the degree: at `deg f = 1` the genus is `0` and the rank
hypothesis is unsatisfiable, and at `deg f = 3` the statement is the Chabauty–Coleman
bound for a rank-zero elliptic curve (`r = 0`, so any odd prime of good reduction does).
Coleman's classical bound is the case `r = genus - 1`, where `p > 2r + 2` reads
`p ≥ deg f` and `2r` reads `2·genus - 2`; the library keeps it as
`ChabautyColeman.main_affine_int`, for integer polynomials.
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
    -- (odd degree makes `y² - f` irreducible), but the `ClassGroup` term below does not
    -- elaborate from Mathlib alone without the instance, so it is taken as a hypothesis.
    [IsDomain (QuadraticAlgebra ℚ[X] f 0)]
    (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive (ClassGroup (QuadraticAlgebra ℚ[X] f 0))) ≤ r) :
    {q : ℚ × ℚ | q.2 ^ 2 = f.eval q.1}.encard + 1
      ≤ ({q : ZMod p × ZMod p
            | (d : ZMod p) * q.2 ^ 2 = (F.map (Int.castRingHom (ZMod p))).eval q.1}.encard + 1)
        + 2 * r := by
  sorry

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
    -- (odd degree makes `y² - f` irreducible), but the `ClassGroup` term below does not
    -- elaborate from Mathlib alone without the instance, so it is taken as a hypothesis.
    [IsDomain (QuadraticAlgebra K[X] f 0)]
    (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive (ClassGroup (QuadraticAlgebra K[X] f 0))) ≤ r) :
    {q : K × K | q.2 ^ 2 = f.eval q.1}.encard + 1
      ≤ ({q : IsLocalRing.ResidueField (v.valuationSubringAtPrime K)
            × IsLocalRing.ResidueField (v.valuationSubringAtPrime K)
            | q.2 ^ 2 = (fA.map (IsLocalRing.residue _)).eval q.1}.encard + 1)
        + 2 * r := by
  sorry

/-- **Finiteness of the rational points over a number field** (blueprint
`cor:finiteness-nf`): for a monic squarefree `f : K[X]` of odd degree over a number field
`K`, under the rank hypothesis the affine `K`-solution set of `y² = f(x)` is finite. No
prime appears: a suitable prime of `𝓞 K` exists for every such `f`. At `K = ℚ` this is the
finiteness of the rational solution set of a monic squarefree rational polynomial of odd
degree under the rank hypothesis. -/
theorem challenge_ratPoints_finite_numberField {K : Type*} [Field K] [NumberField K]
    (f : K[X]) (hf : f.Monic) (hodd : Odd f.natDegree) (hsq : Squarefree f)
    -- The coordinate ring `K[x][y]/(y² - f)` of the curve is a domain; this is a theorem
    -- (odd degree makes `y² - f` irreducible), but the `ClassGroup` term below does not
    -- elaborate from Mathlib alone without the instance, so it is taken as a hypothesis.
    [IsDomain (QuadraticAlgebra K[X] f 0)]
    (hrk : Module.rank ℚ (ℚ ⊗[ℤ] Additive (ClassGroup (QuadraticAlgebra K[X] f 0)))
      < (f.natDegree / 2 : ℕ)) :
    {q : K × K | q.2 ^ 2 = f.eval q.1}.Finite := by
  sorry
