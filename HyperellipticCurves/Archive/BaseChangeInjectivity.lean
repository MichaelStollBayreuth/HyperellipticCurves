/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.BaseChange
public import HyperellipticCurves.Curve.MumfordReduction

/-!
# Base-change injectivity of the Jacobian

A standalone theorem on which the main theorems do not depend — they need only the base-change
*homomorphism* (`ChabautyColeman.HypJac.map`), as the blueprint notes at `lem:eval-factors`. It
is of independent interest: injectivity holds for *arbitrary* field extensions (including
transcendental ones, out of reach of the Galois-descent route of
`HyperellipticCurves.Archive.GaloisAction`), by pure normal-form comparison of reduced Mumford
representatives.

For *every* field extension `K ⊆ K'` (subject to the standing hypotheses on `f` over
both fields), the base-change map `J(K) →* J(K')` is injective
(`ChabautyColeman.hypJac_map_injective`). Classes are compared via their unique reduced
Mumford representatives: base change preserves reduced Mumford data
(`ChabautyColeman.mumfordIdeal_map`), so equal images have equal normal forms over `K'`,
and the coefficients lie in `K`. No finiteness, separability, or characteristic
assumption on the extension is needed.

Blueprint node: `thm:basechange-inj`.
-/

@[expose] public section

open Polynomial nonZeroDivisors

namespace ChabautyColeman

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (f : K[X])
variable [Fact (Odd f.natDegree)]

lemma extendedIdeal_mumfordIdeal {u : K[X]} (hm : u.Monic) (v : K[X]) :
    ClassGroup.extendedIdeal (HypRing K f) (HypRing K' (f.map (algebraMap K K')))
        ⟨mumfordIdeal f u v, mumfordIdeal_mem_nonZeroDivisors f hm.ne_zero v⟩
      = ⟨mumfordIdeal (f.map (algebraMap K K'))
            (u.map (algebraMap K K')) (v.map (algebraMap K K')),
          mumfordIdeal_mem_nonZeroDivisors _ (hm.map _).ne_zero _⟩ :=
  Subtype.ext (mumfordIdeal_map f u v)

variable [NeZero (2 : K)] [Fact (Squarefree f)]
variable [NeZero (2 : K')] [Fact (Squarefree (f.map (algebraMap K K')))]

/-- Base-change injectivity: `J(K) → J(K')` is injective for every field extension
`K ⊆ K'`. Classes are compared via their unique reduced Mumford representatives,
which are preserved by base change. -/
theorem hypJac_map_injective : Function.Injective (HypJac.map (K' := K') f) := by
  intro x₁ x₂ hx
  obtain ⟨u₁, v₁, hm₁, hv₁, hg₁, hd₁, rfl⟩ := exists_mk0_mumfordIdeal_reduced f x₁
  obtain ⟨u₂, v₂, hm₂, hv₂, hg₂, hd₂, rfl⟩ := exists_mk0_mumfordIdeal_reduced f x₂
  rw [HypJac.map, ClassGroup.extendedHom_mk0, ClassGroup.extendedHom_mk0,
    extendedIdeal_mumfordIdeal f hm₁, extendedIdeal_mumfordIdeal f hm₂] at hx
  obtain ⟨hu, hv⟩ := mumfordIdeal_reduced_unique (f.map (algebraMap K K'))
    (hm₁.map _) (hm₂.map _)
    (by rw [degree_map, degree_map]; exact hv₁)
    (by rw [degree_map, degree_map]; exact hv₂)
    (by rw [natDegree_map, natDegree_map]; exact hg₁)
    (by rw [natDegree_map, natDegree_map]; exact hg₂)
    (by simpa using Polynomial.map_dvd (algebraMap K K') hd₁)
    (by simpa using Polynomial.map_dvd (algebraMap K K') hd₂)
    hx
  have hinj := Polynomial.map_injective _ (algebraMap K K').injective
  obtain rfl : u₁ = u₂ := hinj hu
  obtain rfl : v₁ = v₂ := hinj hv
  rfl

end ChabautyColeman

end
