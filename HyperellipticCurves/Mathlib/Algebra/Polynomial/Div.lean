/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# The root multiplicity at `0` of a reflected polynomial; division of `g * v + u` by `g`

## Main statements

* `Polynomial.rootMultiplicity_zero_reflect`: `rootMultiplicity 0 (reflect N p) = N - deg p` for
  `p ≠ 0` with `deg p ≤ N`.
* `Polynomial.self_mul_add_modByMonic`, `Polynomial.self_mul_add_divByMonic`: for monic `g`,
  `(g * v + u) %ₘ g = u %ₘ g` and `(g * v + u) /ₘ g = v + u /ₘ g` (vendored from EllipticCurves,
  `EllipticCurves/Mathlib/Basic.lean`, there `Polynomial.Monic.modByMonic_mul_add` and
  `Polynomial.Monic.divByMonic_mul_add`).

Auxiliary material for the formalization of the Chabauty–Coleman bound and of `2`-descent for
hyperelliptic curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Polynomial

/-- The root multiplicity at `0` of a reflected polynomial: `rootMult 0 (reflect N p) = N - deg p`
for `deg p ≤ N` and `p ≠ 0` (the lowest term of `reflect N p` is `leadingCoeff p · X^(N-deg p)`). -/
theorem rootMultiplicity_zero_reflect {R : Type*} [CommRing R] {p : R[X]} (hp : p ≠ 0) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (reflect N p).rootMultiplicity 0 = N - p.natDegree := by
  have hrefl : reflect N p ≠ 0 := fun h ↦ hp (reflect_eq_zero_iff.mp h)
  rw [rootMultiplicity_eq_natTrailingDegree']
  refine le_antisymm (natTrailingDegree_le_of_ne_zero ?_) (le_natTrailingDegree hrefl fun m hm ↦ ?_)
  · rw [coeff_reflect, revAt_le (by lia), show N - (N - p.natDegree) = p.natDegree by lia]
    exact leadingCoeff_ne_zero.mpr hp
  · rw [coeff_reflect, revAt_le (by lia)]
    exact coeff_eq_zero_of_natDegree_lt (by lia)

end Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

theorem self_mul_add_modByMonic (hg : g.Monic) (v u : R[X]) : (g * v + u) %ₘ g = u %ₘ g := by
  rw [add_modByMonic, self_mul_modByMonic hg, zero_add]

theorem self_mul_add_divByMonic (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g := by
  rw [add_divByMonic, mul_divByMonic_cancel_left v hg]

end Polynomial

end
