/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Prod

/-!
# The apply lemma of `MulEquiv.prodCongr`

## Main statements

* `MulEquiv.prodCongr_apply`, `AddEquiv.prodCongr_apply`: the product of two isomorphisms acts
  componentwise.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

@[to_additive (attr := simp)]
theorem MulEquiv.prodCongr_apply {M N M' N' : Type*} [MulOneClass M] [MulOneClass N]
    [MulOneClass M'] [MulOneClass N'] (f : M ≃* M') (g : N ≃* N') (p : M × N) :
    f.prodCongr g p = (f p.1, g p.2) :=
  rfl

end
