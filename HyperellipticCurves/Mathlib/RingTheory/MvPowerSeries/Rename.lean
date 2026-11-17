/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Coefficients of a renaming along an equivalence

## Main statements

* `MvPowerSeries.coeff_rename_equiv`: the coefficient of `rename e f` at `d` is the coefficient
  of `f` at `d` transported back along `e`.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; an upstreaming candidate for Mathlib.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

theorem coeff_rename_equiv {τ : Type*} (e : σ ≃ τ) (f : MvPowerSeries σ R) (d : τ →₀ ℕ) :
    coeff d (rename (⇑e) f) = coeff (Finsupp.equivMapDomain e.symm d) f := by
  have hemb : Finsupp.embDomain e.toEmbedding = Finsupp.equivMapDomain (M := ℕ) e := by
    funext v
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain]
    rfl
  have hd : Finsupp.embDomain e.toEmbedding (Finsupp.equivMapDomain e.symm d) = d := by
    rw [hemb, ← Finsupp.equivMapDomain_trans, Equiv.symm_trans_self,
      Finsupp.equivMapDomain_refl]
  calc coeff d (rename (⇑e) f)
      = coeff (Finsupp.embDomain e.toEmbedding (Finsupp.equivMapDomain e.symm d))
          (rename (⇑e) f) := by rw [hd]
    _ = coeff (Finsupp.equivMapDomain e.symm d) f := coeff_embDomain_rename _ _ _

end MvPowerSeries

end
