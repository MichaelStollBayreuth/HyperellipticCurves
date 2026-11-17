/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coprime ideals and quotient maps

## Main statements

* `Ideal.map_mk_eq_top_of_sup_eq_top`, `Ideal.exists_mem_mk_eq_of_sup_eq_top`: an ideal coprime
  to `I` maps onto `R ⧸ I`, so it meets every class of `R ⧸ I`.
* `Ideal.ker_eq_sup_of_ker_quotient_lift`: the kernel of a map factoring through `R ⧸ I`,
  computed from the kernel of the induced map on the quotient (the converse direction of
  `Ideal.ker_quotient_lift`).
* `IsIdempotentElem.mul_mem_pow_of_mk_mem_map_pow`: multiplication by an idempotent `ε` brings
  membership in a power of the image of `I` in `A ⧸ (1 - ε)` back down to `A`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An ideal coprime to `I` maps onto the whole quotient ring `R ⧸ I`. -/
theorem Ideal.map_mk_eq_top_of_sup_eq_top {I J : Ideal R} (h : I ⊔ J = ⊤) :
    J.map (Ideal.Quotient.mk I) = ⊤ := by
  rw [← Ideal.map_top (Ideal.Quotient.mk I), ← h, Ideal.map_sup, Ideal.map_quotient_self,
    bot_sup_eq]

/-- An ideal coprime to `I` contains a representative of every class of `R ⧸ I`. -/
theorem Ideal.exists_mem_mk_eq_of_sup_eq_top {I J : Ideal R} (h : I ⊔ J = ⊤) (γ : R ⧸ I) :
    ∃ c ∈ J, Ideal.Quotient.mk I c = γ :=
  Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp
    (by rw [Ideal.map_mk_eq_top_of_sup_eq_top h]; trivial)

/-- The kernel of a map `f` vanishing on `I`, read off from the kernel of the induced map on
`R ⧸ I`; the converse direction of `Ideal.ker_quotient_lift`. -/
theorem Ideal.ker_eq_sup_of_ker_quotient_lift {I : Ideal R} (f : R →+* S) (h : ∀ a ∈ I, f a = 0)
    {K : Ideal R} (hk : RingHom.ker (Ideal.Quotient.lift I f h) = K.map (Ideal.Quotient.mk I)) :
    RingHom.ker f = I ⊔ K := by
  have hI : I ≤ RingHom.ker f := fun a ha ↦ RingHom.mem_ker.mpr (h a ha)
  have := congrArg (Ideal.comap (Ideal.Quotient.mk I))
    ((Ideal.ker_quotient_lift f h).symm.trans hk)
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_of_le_left hI, sup_comm] at this

end

section

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- Multiplication by an idempotent `ε` splits membership in a power of the image of `I` in
`A ⧸ (1 - ε)` back down to `A`: it kills the ambiguity `(1 - ε)A` of a lift. -/
theorem IsIdempotentElem.mul_mem_pow_of_mk_mem_map_pow {A : Type*} [CommRing A] {ε : A}
    (hε : IsIdempotentElem ε) (I : Ideal A) {x : A} {n : ℕ}
    (hx : Ideal.Quotient.mk (Ideal.span {1 - ε}) x ∈
      I.map (Ideal.Quotient.mk (Ideal.span {1 - ε})) ^ n) :
    ε * x ∈ I ^ n := by
  rw [← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker] at hx
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hx
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
  have hεc : ε * ((1 - ε) * d) = 0 := by
    rw [← mul_assoc, mul_sub, mul_one, hε.eq, sub_self, zero_mul]
  rw [show ε * x = ε * a by rw [← hac, mul_add, hεc, add_zero]]
  exact Ideal.mul_mem_left _ _ ha

end

end
