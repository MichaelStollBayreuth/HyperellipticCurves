# HyperellipticCurves

[![Website](https://img.shields.io/badge/Website-ready-green)](https://michaelstollbayreuth.github.io/HyperellipticCurves/)
[![Blueprint](https://img.shields.io/badge/Blueprint-complete-green)](https://michaelstollbayreuth.github.io/HyperellipticCurves/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/Blueprint-PDF-blue)](https://michaelstollbayreuth.github.io/HyperellipticCurves/blueprint.pdf)
[![Documentation](https://img.shields.io/badge/Documentation-API-green)](https://michaelstollbayreuth.github.io/HyperellipticCurves/docs/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A formalization in [Lean 4](https://lean-lang.org), based on
[Mathlib](https://github.com/leanprover-community/mathlib4), of the method of Chabauty and
Coleman for hyperelliptic curves `C : y² = f(x)` with `f` monic of odd degree `2g + 1`, in the
refined form of

> M. Stoll, *Independence of rational points on twists of a given curve*,
> Compositio Math. **142** (2006), 1201–1214
> ([DOI: 10.1112/S0010437X06002168](https://doi.org/10.1112/S0010437X06002168)),

Theorem 6.4 and Corollary 6.7. Over `ℚ` the result reads: if `f ∈ ℚ[x]` is monic of odd degree
`2g + 1`, the rank `dim_ℚ (J(ℚ) ⊗ ℚ)` of the Jacobian is at most `r < g`, and `p > 2r + 2` is a
prime at which `f` is integral with squarefree reduction, then

```
#C(ℚ) ≤ #C̄(𝔽_p) + 2r
```

(`ChabautyColeman.main_affine_rat_of_rank_le`). The case `r = g − 1` is Coleman's bound
`#C(ℚ) ≤ #C̄(𝔽_p) + 2g − 2` for `p > 2g` (R. F. Coleman, *Effective Chabauty*, Duke Math. J.
**52** (1985), 765–770, [DOI: 10.1215/S0012-7094-85-05240-8](https://doi.org/10.1215/S0012-7094-85-05240-8);
`ChabautyColeman.main_affine_int` for `f ∈ ℤ[x]`). The rank is a cardinal: finite generation of
`J(ℚ)` is not assumed, and no lower bound on the genus either (genus 1, that is, elliptic
curves of rank 0, is included).

The same bound holds over every number field `K`, at a prime `𝔭` at which `f` is integral with
squarefree reduction, with the count taken over the residue field of `𝔭` and the condition
`p > 2r + e + 1` on the residue characteristic `p`, `e` being the ramification index
(`ChabautyColeman.NumberFieldBase.main_affine_numberField`, for the fraction field of any
Dedekind domain that is finite free over `ℤ`). Its corollary is the finiteness of `C(K)` when
the rank is smaller than the genus (`ChabautyColeman.NumberFieldBase.ratPoints_finite_numberField`).
Both are instances of the main theorem `ChabautyColeman.chabauty_coleman_odd_hyperelliptic`,
which is stated over an abstract complete discrete valuation ring of characteristic 0 with
algebraically closed residue field of characteristic `≠ 2`, a uniformizer `π` and a bound `e` on
the absolute ramification index; over a number field, that ring is constructed as a direct
factor of `W(𝔽̄_p) ⊗ A`.

Mathlib has no Jacobian varieties, so the formalization works with a ring-theoretic model: the
Jacobian is the ideal class group of the affine coordinate ring `K[x, y]/(y² − f)`, with reduced
Mumford representatives and Cantor's algorithm; the reduction of classes is constructed by
reducing points, through a specialization theorem for principal divisors; and the `p`-adic
logarithm on the kernel of reduction is the logarithm of a formal group law built from Cantor's
algorithm at a translate of the origin, whose differentials are identified with the regular
differentials by a trace-form computation. The [blueprint](#blueprint) explains the
construction.

## Contents

The Lean sources are in [`HyperellipticCurves`](HyperellipticCurves) (namespace
`ChabautyColeman`):

- [`Curve`](HyperellipticCurves/Curve): hyperelliptic curves, the coordinate ring as a Dedekind
  domain, the Jacobian as its class group, Mumford representation and the classes of Mumford
  ideals, base change, and the cited structure results on the Jacobian that the descent uses;
- [`Series`](HyperellipticCurves/Series): the `p`-adic power-series kit — evaluation on the
  maximal ideal, Weierstrass preparation, Strassmann's theorem, interpolation, formal group laws
  and their logarithms;
- [`Disks`](HyperellipticCurves/Disks): residue disks and their parametrizations, the expansions
  of differentials, orders of vanishing, and the vanishing budget of a space of differentials
  (Stoll's Theorem 6.4);
- [`Specialization`](HyperellipticCurves/Specialization) and [`RedJ`](HyperellipticCurves/RedJ):
  the specialization of principal divisors and the reduction homomorphism on classes, with its
  kernel `J¹`;
- [`Log`](HyperellipticCurves/Log): the logarithm — Cantor's algorithm as polynomial identities
  with certificates (`Cantor`), the auxiliary class `τ` in general position (`Witness`, `Fold`),
  the translated formal group law `F_τ` (`Ftau`), the charts on residue disks (`Charts`), the
  trace-form computation of the differentials (`Trace`), and the logarithm and the pairing `λ`
  (`Analytic`);
- [`Count`](HyperellipticCurves/Count): the annihilating differentials, the bound per residue
  disk, the main theorems, and their instantiations over number fields and over `ℚ`;
- [`Descent`](HyperellipticCurves/Descent): `2`-descent on the Jacobian — the `x - T` map
  `J(K) → L^× / (L^×)²`, `L = K[x]/(f)`, with kernel `2 J(K)` (through certificates for halving
  points), its image in the Selmer group over the fraction field of a Dedekind domain, the
  `2`-Selmer group and the bound on the rank over a number field (with the Mordell–Weil theorem
  and Mattuck's theorem as cited inputs), and two examples of genus `2` over `ℚ`; the main
  theorems do not depend on it;
- [`Mathlib`](HyperellipticCurves/Mathlib): auxiliary declarations missing from Mathlib, stated
  in their natural generality; these are candidates for upstreaming. The folder mirrors Mathlib's
  file structure: `Mathlib/X/Y.lean` holds the declarations whose eventual home is the Mathlib
  file `Mathlib/X/Y.lean`;
- [`Archive`](HyperellipticCurves/Archive): statements that are formalized and built with the
  library but that the main theorems do not depend on — among them base-change injectivity of
  the Jacobian, the finite index of the kernel of reduction, and the formal exponential; the
  blueprint marks each of them. The auxiliary declarations that only the Archive uses are in the
  mirror tree [`Archive/Mathlib`](HyperellipticCurves/Archive/Mathlib).

[`formalization.yaml`](formalization.yaml) is the project's self-report in the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) format; it
includes a table aligning the results of the source papers with the declarations that formalize
them. [`comparator/`](comparator) holds a [comparator](https://github.com/leanprover/comparator)
harness that certifies the main results independently of the repository's own build; see
[Checking the results with comparator](#checking-the-results-with-comparator).
[`prototype/`](prototype) holds the Magma and Python scripts cited in the blueprint and in the
sources, which check statements symbolically or numerically at small genus; see
[`prototype/README.md`](prototype/README.md).

## Blueprint

[`blueprint/`](blueprint) contains a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
blueprint that develops the mathematics, with statements and proofs, and links each item to the
declarations that formalize it: the class-group model of the Jacobian (chapter 1), the `p`-adic
power-series kit (chapter 2), residue disks and the reduction of classes (chapter 3), the
logarithm (chapter 4), the count (chapter 5), the theorem over number fields (chapter 6), and
`2`-descent (chapter 7).
Every node of the dependency graph is formalized.

To build it, install [leanblueprint](https://github.com/PatrickMassot/leanblueprint) and a TeX
distribution, then run in the root directory of this repository

```bash
leanblueprint pdf                          # blueprint/print/print.pdf
leanblueprint web                          # blueprint/web/index.html
lake build Challenge Solution              # needed by the next step
lake exe checkdecls blueprint/lean_decls   # every \lean{...} name exists
```

`checkdecls` reads `blueprint/lean_decls`, which `leanblueprint web` writes, and imports the
roots of all libraries of the package, the comparator libraries included. The web version must
be viewed over HTTP (`leanblueprint serve`), not opened as a local file: the dependency graph is
rendered by a WebAssembly build of Graphviz in a web worker, which browsers block on `file://`
URLs.

## API documentation

```bash
lake build HyperellipticCurves:docs   # .lake/build/doc/index.html
```

generates the documentation with [doc-gen4](https://github.com/leanprover/doc-gen4), which is
required by `lakefile.toml` for this purpose only (a plain `lake build` does not build it; keep
its `rev` in sync with `lean-toolchain`). The documentation covers everything the project
imports, that is, all of Mathlib: doc-gen4 walks the import closure by construction.

The [Pages workflow](.github/workflows/deploy-pages.yml) builds the blueprint and the
documentation and publishes them alongside a short project page (sources in
[`website/`](website)) at <https://michaelstollbayreuth.github.io/HyperellipticCurves/>. It runs
on every push to `main`, and can also be triggered by hand.

## Building

Ensure that you have a functioning Lean 4 installation (see the
[Lean installation guide](https://leanprover-community.github.io/get_started.html)), then run

```bash
lake exe cache get
lake build
```

in the root directory of this repository.

## Checking the results with comparator

[Comparator](https://github.com/leanprover/comparator), built into Lake as `lake comparator` since
Lean v4.35.0, certifies that a Lean development proves a given list of statements. The statements
are in [`comparator/Challenge.lean`](comparator/Challenge.lean), which imports **only Mathlib**
and states the three headline results with `sorry` proofs: the bound over `ℚ`, the bound over a
number field, and the finiteness of the rational points over a number field. Comparator checks
that [`comparator/Solution.lean`](comparator/Solution.lean) proves exactly these statements, that
the proofs use no axioms beyond `propext`, `Quot.sound` and `Classical.choice`, and that the Lean
kernel accepts them.

After `lake exe cache get` (see [Building](#building)), run in the root directory of this
repository

```bash
scripts/run-comparator.sh
```

The script builds the library (`lake build HyperellipticCurves`) and then runs
`lake comparator --config comparator/challenges.json`, which builds and exports the challenge and
the solution inside a sandbox; this needs [bubblewrap](https://github.com/containers/bubblewrap)
(`bwrap`) with unprivileged user namespaces. A run that passes ends with `Your solution is okay!`
and exit code `0`. [`comparator/README.md`](comparator/README.md) has the details.
