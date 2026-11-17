/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling `Mathlib.RingTheory.Ideal.Operations`: `Module.Basis`, for the statement of
-- `Module.Basis.mem_smul_top_iff`.
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Ideals acting on modules, and sums with principal ideals

## Main statements

* `Ideal.sup_span_singleton_eq_of_sub_mem`: adjoining `x` or `y` to `I` gives the same ideal as
  soon as `x - y ∈ I`.
* `Ideal.smul_top_eq_self`: an ideal `K` of `R`, viewed as a submodule, satisfies `K • ⊤ = K`.
* `Module.Basis.mem_smul_top_iff`: membership in `K • ⊤` of a module with a finite basis is
  coordinatewise membership in `K`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Adjoining `x` or `y` to `I` gives the same ideal as soon as `x - y ∈ I`. -/
theorem Ideal.sup_span_singleton_eq_of_sub_mem {I : Ideal R} {x y : R} (h : x - y ∈ I) :
    I ⊔ Ideal.span {x} = I ⊔ Ideal.span {y} := by
  have key (u v : R) (huv : u - v ∈ I) : I ⊔ Ideal.span {u} ≤ I ⊔ Ideal.span {v} := by
    refine sup_le le_sup_left ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, show u = v + (u - v) by ring]
    exact Submodule.add_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      (Ideal.mem_sup_left huv)
  exact le_antisymm (key x y h) (key y x (by simpa using neg_mem h))

end

section

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- An ideal `K` of `R`, viewed as a submodule of `R`, absorbs all of `R`: `K • ⊤ = K`. -/
theorem Ideal.smul_top_eq_self (K : Ideal R) : (K • ⊤ : Submodule R R) = K := by
  rw [smul_eq_mul, Ideal.mul_top]

section AdicBasis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Membership in `K • ⊤` of a free module is coordinatewise membership in `K`. -/
theorem Module.Basis.mem_smul_top_iff {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (K : Ideal R) (x : M) : x ∈ (K • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ K := by
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun hx i ↦ ?_, fun h ↦ ?_⟩
  · refine Submodule.smul_induction_on hx (fun k hk m _ ↦ ?_) (fun y z hy hz ↦ ?_)
    · rw [map_smul]
      exact K.mul_mem_right _ hk
    · rw [map_add, Finsupp.add_apply]
      exact K.add_mem hy hz
  · rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (h i) Submodule.mem_top

end AdicBasis

end

end
