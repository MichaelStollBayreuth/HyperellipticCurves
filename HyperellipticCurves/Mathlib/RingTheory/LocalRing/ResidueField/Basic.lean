/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Reductions of a basis of a saturated submodule

## Main statements

* `IsLocalRing.linearIndependent_map_of_saturated`: for a submodule `N` saturated with respect
  to an element `π` of the maximal ideal (`π • w ∈ N → w ∈ N`) and a linear map `f` into a
  module over the residue field whose kernel consists of multiples of `π`, the images under `f`
  of a basis of `N` are linearly independent over the residue field.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

open Module

namespace IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {M : Type*} [AddCommGroup M] [Module O M]
  {M' : Type*} [AddCommGroup M'] [Module O M'] [Module (ResidueField O) M']
  [IsScalarTower O (ResidueField O) M']

/-- **The reductions of a basis of a saturated submodule are linearly independent.** Here
`N` is a submodule of `M` saturated with respect to an element `π` of the maximal ideal
(`π • w ∈ N → w ∈ N`), and `f` is a linear map into a module over the residue field whose
kernel consists of multiples of `π`. A combination of the basis `bb` of `N` whose image
under `f` vanishes is `π` times an element of `M`, hence — by saturation — `π` times an
element of `N`, so all its coordinates are divisible by `π` and their residues vanish. -/
theorem linearIndependent_map_of_saturated {ι : Type*} [Finite ι] {N : Submodule O M} {π : O}
    (hπ : π ∈ maximalIdeal O) (bb : Basis ι O N) (hsat : ∀ w : M, π • w ∈ N → w ∈ N)
    (f : M →ₗ[O] M') (hker : ∀ v : M, f v = 0 → ∃ w : M, v = π • w) :
    LinearIndependent (ResidueField O) fun i ↦ f (bb i : M) := by
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  choose c' hc' using fun i ↦ residue_surjective (R := O) (c i)
  set v : N := ∑ i, c' i • bb i with hv
  have hvcoe : (v : M) = ∑ i, c' i • (bb i : M) := by rw [hv]; simp
  have hv0 : f (v : M) = 0 := by
    rw [hvcoe, map_sum, ← hc]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [map_smul, ← hc' j, ← ResidueField.algebraMap_eq, algebraMap_smul]
  obtain ⟨w, hw⟩ := hker _ hv0
  have hwN : w ∈ N := hsat w (by rw [← hw]; exact v.2)
  have hvw : v = π • (⟨w, hwN⟩ : N) := Subtype.ext (by rw [hw]; rfl)
  have hrepr : ⇑(bb.repr v) = c' := by rw [hv]; exact bb.repr_sum_self c'
  have hci : c' i = π * bb.repr ⟨w, hwN⟩ i := by rw [← congrFun hrepr i, hvw, map_smul]; simp
  rw [← hc' i, hci, map_mul, (residue_eq_zero_iff _).mpr hπ, zero_mul]

end IsLocalRing

end
