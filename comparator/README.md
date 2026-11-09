# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator) — "a trustworthy judge
for Lean proofs", built into Lake as `lake comparator` since Lean v4.35.0 — certify that this
repository proves its headline results, independently of the repository's own build and using only
the permitted axioms:

* the **Chabauty–Coleman bound over `ℚ`** (blueprint `thm:main`,
  `ChabautyColeman.main_affine_rat_of_rank_le`): for a monic `f ∈ ℚ[x]` of odd degree with
  `p`-integral coefficients — `d·f = F ∈ ℤ[x]` with `p ∤ d` — whose reduction mod the prime
  `p` is squarefree, under the rank hypothesis `rk J(ℚ) ≤ r` with `r < g = ⌊deg f / 2⌋` and
  the prime condition `p > 2r + 2`, the number of rational points of `y² = f(x)` is at most
  the number of points of the reduced model `d·y² = F(x)` over `𝔽_p`, plus `2r` (Coleman's
  `2g − 2` for `p ≥ deg f` is the case `r = g − 1`, for `f ∈ ℤ[x]`);
* the **bound over a number field** (blueprint `thm:main-nf`,
  `ChabautyColeman.NumberFieldBase.main_affine_numberField`; Stoll, Compositio Math. 142
  (2006), Cor. 6.7): the same bound over a number field `K` for monic `f ∈ K[x]` with
  `v`-integral coefficients and squarefree reduction at a prime `v` of `𝓞 K`, with the prime
  condition `p > 2r + e + 1` for the residue characteristic `p` and the ramification index
  `e`, and the count over the residue field of `v`;
* its corollary, **finiteness of the rational points** (blueprint `cor:finiteness-nf`,
  `ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField`) — with no prime in the
  statement: `f ∈ K[x]` monic, squarefree and of odd degree, and the rank hypothesis; at
  `K = ℚ` this is the finiteness of the rational solution set of a monic squarefree rational
  polynomial of odd degree under the rank hypothesis.

## What is checked

- [`Challenge.lean`](Challenge.lean) imports **only Mathlib** and states all three results with
  `sorry` proofs — over `ℚ` for a polynomial `f : ℚ[X]`, a prime `p`, an integral model
  `F : ℤ[X]`, `d : ℤ` with `p ∤ d` and `F = d·f`, and a rank bound `r : ℕ`; over a number field
  `K` (`[NumberField K]`) for `f : K[X]`, a prime `v : HeightOneSpectrum (𝓞 K)` and an integral
  model `fA` of `f` over the ring of `v`-integers `v.valuationSubringAtPrime K`, with the
  residue characteristic spelled `ringChar` of the residue field of that ring and the
  ramification index `Ideal.ramificationIdx' (v.asIdeal.under ℤ) v.asIdeal` — nothing else. The
  hypotheses of the two bounds are: `f` monic of odd degree, squarefree reduction (`F mod p`,
  resp. `fA mod v`), `r < ⌊deg f / 2⌋`, the rank hypothesis `≤ r`, and the prime condition
  `p > 2r + 2`, resp. `p > 2r + e + 1`; the finiteness statement has no prime at all — it asks
  that `f` be squarefree over `K` and takes the rank hypothesis in the sharp form
  `rank < f.natDegree / 2`. Every notion is a Mathlib definition: the coordinate ring of the
  curve is `QuadraticAlgebra K[X] f 0` (`K[x][y]/(y² − f)`), its Jacobian is Mathlib's
  `ClassGroup` of that ring, the rank is the `Module.rank` of the `ℚ`-tensored class group, the
  genus is spelled `f.natDegree / 2`, and the point counts are `Set.encard` of the affine
  solution sets of `y² = f(x)` in `ℚ × ℚ`, resp. `K × K`, and of the reduced model in
  `ZMod p × ZMod p`, resp. in the square of the residue field of `v`, each side incremented by
  `1` for the point at infinity. One deliberate
  deviation: the fact that the coordinate ring is a domain (a theorem of the library) is carried
  as an instance hypothesis so that `ClassGroup` elaborates from Mathlib alone. There is no genus
  lower bound: degree `1` makes the rank hypothesis unsatisfiable, and degree `3` (rank-zero
  elliptic curves) is included.
- [`Solution.lean`](Solution.lean) imports `HyperellipticCurves.Count.NumberField` and
  `HyperellipticCurves.Count.Arithmetic` and proves those statements by the library theorems — the
  instantiation of the abstract main theorems at the local direct factor `O` of
  `𝕎(𝔽̄_p) ⊗ 𝓞 K` with `K₀ = K` and `O₀` the ring of `v`-integers of `K`, and its case
  `A = ℤ`, `K = ℚ`, `v = (p)` for the bound over `ℚ`.

`lake comparator` builds and exports both modules inside a `bubblewrap` sandbox (it never loads
the project's `.olean`s into its own process) and checks that each challenge theorem in the
solution:

1. proves the **same statement** as in the challenge — comparing the full bodies (not just the
   types) of every definition the statement transitively refers to (here, all from Mathlib);
2. uses no axioms beyond `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`);
3. is accepted by the Lean kernel.

## Config

[`challenges.json`](challenges.json) — theorems `challenge_main_affine`,
`challenge_main_affine_numberField` and `challenge_ratPoints_finite_numberField`.

## Running

Run from the **repository root**; the only prerequisite besides Lean is `bubblewrap` (`bwrap`)
with unprivileged user namespaces (or installed setuid root):

```bash
scripts/run-comparator.sh               # = lake build HyperellipticCurves && lake comparator --config comparator/challenges.json
scripts/run-comparator.sh --paranoid    # also run all external checkers bundled with Lean
```

Exit code `0` (and `Your solution is okay!`) means the check passed, `1` that it was rejected, `2`
that it could not start (no `bwrap`, no `lake-manifest.json`, a malformed configuration). The
wrapper builds the library first: the sandbox cannot write to the project directory, and with a
current build the sandboxed builds only replay it.

The `Challenge`/`Solution` libraries are declared in the root `lakefile.toml` but are excluded from
`defaultTargets`, so a plain `lake build` does not build them and the deliberate `sorry` in
`Challenge.lean` never enters the library build.
