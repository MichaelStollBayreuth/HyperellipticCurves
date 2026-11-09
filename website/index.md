---
layout: default
title: HyperellipticCurves
---

<header class="page-header">
  <h1>{{ site.title }}</h1>
</header>

A formalization in [Lean 4](https://lean-lang.org), based on
[Mathlib](https://github.com/leanprover-community/mathlib4), of the method of Chabauty and
Coleman for hyperelliptic curves `C : y² = f(x)` with `f` monic of odd degree `2g + 1`. If the
Jacobian `J` of `C` over a number field `K` has rank at most `r < g`, then

> `#C(K) ≤ #C̄(k) + 2r`

at every prime of good reduction whose residue field is `k` and whose residue characteristic `p`
satisfies `p > 2r + e + 1`, `e` being the ramification index. Over `ℚ` this reads
`#C(ℚ) ≤ #C̄(𝔽_p) + 2r` for `p > 2r + 2`; the case `r = g − 1` is Coleman's bound, and the
improvement to `2r` is Theorem 6.4 and Corollary 6.7 of

> [Michael Stoll](https://www.mathe2.uni-bayreuth.de/stoll/),
> *Independence of rational points on twists of a given curve*,
> Compositio Math. **142** (2006), 1201–1214
> ([DOI: 10.1112/S0010437X06002168](https://doi.org/10.1112/S0010437X06002168)).

Mathlib has no Jacobian varieties, so the Jacobian is modelled as the ideal class group of the
affine coordinate ring, and the `p`-adic logarithm on it is built from a formal group law
obtained from Cantor's algorithm.

- [Blueprint]({{ site.baseurl }}/blueprint/) — the mathematics, with each definition and
  statement linked to the declaration that formalizes it
  ([PDF version]({{ site.baseurl }}/blueprint.pdf))
- [API documentation]({{ site.baseurl }}/docs/) — generated from the Lean sources
- [Source code](https://github.com/MichaelStollBayreuth/HyperellipticCurves) on GitHub
