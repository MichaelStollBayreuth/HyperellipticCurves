/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Finite modules over a complete Noetherian ring are complete

## Main statements

* `isAdicComplete_of_finite`: a finite module over an `I`-adically complete Noetherian ring is
  `I`-adically complete (via `AdicCompletion.ofTensorProduct`; single-universe, as is that
  map).

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

section FiniteModule

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
  (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over an `I`-adically complete Noetherian ring is itself `I`-adically
complete. (Single-universe, inherited from `AdicCompletion.ofTensorProduct`.) -/
theorem isAdicComplete_of_finite : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  have hR : Function.Bijective (AdicCompletion.of I R) :=
    AdicCompletion.of_bijective_iff.mpr ‹_›
  have hT : Function.Bijective (AdicCompletion.ofTensorProduct I M) :=
    AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M
  have h1 : AdicCompletion.of I R 1 = 1 := by
    have := AdicCompletion.algebraMap_apply (I := I) (S := R) 1
    simpa using this.symm
  set eR : R ≃ₗ[R] AdicCompletion I R := LinearEquiv.ofBijective _ hR with heR
  have hcomp : ⇑(AdicCompletion.of I M)
      = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑(LinearEquiv.rTensor M eR)
        ∘ ⇑(TensorProduct.lid R M).symm := by
    funext x
    simp only [Function.comp_apply, TensorProduct.lid_symm_apply, LinearEquiv.rTensor_tmul,
      AdicCompletion.ofTensorProduct_tmul]
    rw [heR]
    change _ = AdicCompletion.of I R 1 • AdicCompletion.of I M x
    rw [h1, one_smul]
  rw [hcomp]
  exact hT.comp ((eR.rTensor M).bijective.comp (TensorProduct.lid R M).symm.bijective)

end FiniteModule

end
