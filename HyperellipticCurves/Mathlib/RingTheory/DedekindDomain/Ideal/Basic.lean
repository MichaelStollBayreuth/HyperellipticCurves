/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Multiplicities of maximal ideals in a Dedekind domain

## Main statements

* `Ideal.emultiplicity_eq_zero_of_isMaximal_of_ne`: distinct maximal ideals of a Dedekind domain
  do not divide one another.
* `Ideal.emultiplicity_self_of_ne_top`: a proper nonzero ideal of a Dedekind domain occurs in
  itself with multiplicity one.

Auxiliary material for the formalization of the Chabauty–Coleman bound for hyperelliptic
curves; upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Distinct maximal ideals of a Dedekind domain do not divide one another. -/
theorem emultiplicity_eq_zero_of_isMaximal_of_ne {P Q : Ideal R} (hP : P.IsMaximal)
    (hQ : Q.IsMaximal) (hne : Q ≠ P) : emultiplicity P Q = 0 :=
  emultiplicity_eq_zero.mpr fun hdvd ↦ hne (hQ.eq_of_le hP.ne_top (Ideal.dvd_iff_le.mp hdvd))

/-- A proper nonzero ideal of a Dedekind domain occurs in itself with multiplicity one. -/
theorem emultiplicity_self_of_ne_top {P : Ideal R} (hP : P ≠ ⊤) (h0 : P ≠ ⊥) :
    emultiplicity P P = 1 :=
  (finiteMultiplicity hP h0).emultiplicity_self

end Ideal

end
