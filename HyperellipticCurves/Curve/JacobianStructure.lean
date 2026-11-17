/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.Jacobian
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

import HyperellipticCurves.Mathlib.GroupTheory.IndexNSmul
import HyperellipticCurves.Mathlib.GroupTheory.Torsion
import HyperellipticCurves.Mathlib.NumberTheory.Padics.RingHoms

/-!
# The structure of `J(K)`, cited

Three results from the literature on the group `J(K)` of the Jacobian of `y ^ 2 = f(x)` enter as
cited statements: the Mordell-Weil theorem over a number field, Mattuck's description of `J(F)` for
a finite extension `F` of `ℚ_[p]` (blueprint `def:ds-cited`), and the injectivity of reduction
modulo a good odd prime on the torsion of `J(ℚ)` (the cited input (Red) of the examples, blueprint
`def:ds-red`). From Mattuck's description: the size of `J(F) / 2 J(F)` and the elements of `J(F)`
divisible by every power of `p`.

## Main definitions

* `ChabautyColeman.HypJac.MordellWeil K f`: `J(K)` is finitely generated, for a number field `K`.
* `ChabautyColeman.HypJac.LocalStructure p F f g`: `J(F) ≅ O ^ g × T` with `O` the ring of
  integers of `F` (as a group, `ℤ_[p] ^ [F : ℚ_[p]]`) and `T` finite.
* `ChabautyColeman.HypJac.TorsionReduction p F`: for `F : ℤ[X]`, a homomorphism from `J(ℚ)` to the
  Jacobian over `ZMod p` of the reduction of `F` that is injective on the elements of finite order.

## Main statements

* `ChabautyColeman.HypJac.LocalStructure.card_modPow_two`: `#J(F) / 2 J(F) = 2 ^ (g d) * #J(F)[2]`
  for `F` of degree `d` over `ℚ_[2]`.
* `ChabautyColeman.HypJac.LocalStructure.card_modPow_two_of_ne_two`: `#J(F) / 2 J(F) = #J(F)[2]`
  over an extension of `ℚ_[p]` for `p ≠ 2`.
* `ChabautyColeman.HypJac.LocalStructure.mem_iInf_range_powMonoidHom_pow_iff`: the elements of
  `J(F)` that are `p ^ n`-th powers for every `n` are those of order prime to `p`.
* `ChabautyColeman.HypJac.LocalStructure.mem_iInf_range_powMonoidHom_two_pow_iff`: for `p = 2`,
  those of odd order.
* `ChabautyColeman.HypJac.TorsionReduction.pow_eq_one_of_isOfFinOrder`: an exponent of the group
  over `ZMod p` kills every element of finite order of `J(ℚ)`.

## Implementation notes

The cited statements are a class and two structures whose docstrings give the references;
`ChabautyColeman.HypJac.MordellWeil` is a class, so that it provides `IsMulFG (HypJac K f)` as an
instance.
-/

@[expose] public section

open Polynomial Module

namespace ChabautyColeman

/-- **The Mordell-Weil theorem** for the Jacobian of `y ^ 2 = f(x)` over a number field `K`:
`J(K)` is finitely generated. Cited, not proved: A. Weil, *L'arithmétique sur les courbes
algébriques*, Acta Math. 52 (1929), 281–315; for abelian varieties over number fields, M. Hindry
and J. H. Silverman, *Diophantine geometry. An introduction*, GTM 201, Springer, 2000,
Theorem C.0.1 on p. 257. -/
class HypJac.MordellWeil (K : Type*) [Field K] [NumberField K] (f : K[X])
    [Fact (Odd f.natDegree)] [Fact (Squarefree f)] : Prop where
  /-- `J(K)` is finitely generated. -/
  isMulFG : IsMulFG (HypJac K f)

attribute [instance] HypJac.MordellWeil.isMulFG

/-- **The structure of `J(F)`** for the Jacobian of `y ^ 2 = f(x)`, of genus `g`, over a finite
extension `F` of `ℚ_[p]`, of degree `d`: `J(F) ≅ O ^ g × T` as groups, with `O` the ring of
integers of `F` and `T` a finite group. As a group, `O ≅ ℤ_[p] ^ d`, so the statement says
`J(F) ≅ (ℤ_[p] ^ d) ^ g × T`; `T` is written additively. Cited, not proved: A. Mattuck, *Abelian
varieties over `p`-adic ground fields*, Ann. of Math. (2) 62 (1955), 92–119, where the
isomorphism is one of topological groups; for `F = ℚ_[2]` also B. Poonen and M. Stoll, *Most odd
degree hyperelliptic curves have only one rational point*, Ann. of Math. (2) 180 (2014),
1137–1166, Section 4, p. 1145. -/
structure HypJac.LocalStructure (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F]
    (f : F[X]) [Fact (Odd f.natDegree)] [Fact (Squarefree f)] (g : ℕ) : Prop where
  /-- The curve has genus `g`. -/
  natDegree_eq : f.natDegree = 2 * g + 1
  /-- `J(F) ≅ (ℤ_[p] ^ d) ^ g × T` with `d = [F : ℚ_[p]]` and `T` finite. -/
  exists_mulEquiv : ∃ (T : Type) (_ : AddCommGroup T), Finite T ∧
    Nonempty (HypJac F f ≃* Multiplicative ((Fin g → Fin (finrank ℚ_[p] F) → ℤ_[p]) × T))

namespace HypJac.LocalStructure

variable {g : ℕ}

section Prime

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Algebra ℚ_[p] F] {f : F[X]}
  [Fact (Odd f.natDegree)] [Fact (Squarefree f)]

-- The size of `J(F) / 2 J(F)` in terms of `#J(F)[2]` and the index of `2 ℤ_[p]`.
private theorem card_modPow_two_eq (L : LocalStructure p F f g) :
    Nat.card (HypJac F f ⧸ (powMonoidHom 2 : HypJac F f →* HypJac F f).range) =
      (nsmulAddMonoidHom (α := ℤ_[p]) 2).range.index ^ (finrank ℚ_[p] F * g) *
        Nat.card (powMonoidHom 2 : HypJac F f →* HypJac F f).ker := by
  obtain ⟨T, _, _, ⟨e⟩⟩ := L.exists_mulEquiv
  rw [← Subgroup.index_eq_card]
  change (nsmulAddMonoidHom (α := Additive (HypJac F f)) 2).range.index =
    _ * Nat.card (nsmulAddMonoidHom (α := Additive (HypJac F f)) 2).ker
  rw [(MulEquiv.toAdditiveLeft e).index_range_nsmulAddMonoidHom,
    (MulEquiv.toAdditiveLeft e).card_ker_nsmulAddMonoidHom,
    AddSubgroup.index_range_nsmul_prod_of_injective
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree two_ne_zero),
    AddSubgroup.index_range_nsmul_pi, AddSubgroup.index_range_nsmul_pi, Fintype.card_fin,
    Fintype.card_fin, pow_mul]

/-- **The size of `J(F) / 2 J(F)` over a `p`-adic field** for `p ≠ 2`: `#J(F)[2]`. -/
theorem card_modPow_two_of_ne_two (L : LocalStructure p F f g) (hp : p ≠ 2) :
    Nat.card (HypJac F f ⧸ (powMonoidHom 2 : HypJac F f →* HypJac F f).range) =
      Nat.card (powMonoidHom 2 : HypJac F f →* HypJac F f).ker := by
  rw [L.card_modPow_two_eq, PadicInt.range_nsmul_eq_top_of_not_dvd
    ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).not.mpr hp), AddSubgroup.index_top,
    one_pow, one_mul]

/-- **The elements of `J(F)` divisible by every power of `p`** are those of finite order prime to
`p`. -/
theorem mem_iInf_range_powMonoidHom_pow_iff (L : LocalStructure p F f g) {x : HypJac F f} :
    x ∈ ⨅ n : ℕ, (powMonoidHom (p ^ n) : HypJac F f →* HypJac F f).range ↔
      (orderOf x).Coprime p := by
  refine ⟨fun hx ↦ ?_, fun h ↦ Subgroup.mem_iInf.mpr fun n ↦
    CommGroup.mem_range_powMonoidHom_of_coprime (h.pow_right n)⟩
  obtain ⟨T, _, _, ⟨e⟩⟩ := L.exists_mulEquiv
  refine MonoidHom.coprime_orderOf_of_mem_iInf_range_powMonoidHom_pow (f := e.toMonoidHom)
    e.injective (fun y hy ↦ ?_) hx
  rw [← ofAdd_toAdd y, orderOf_ofAdd_eq_addOrderOf]
  refine (AddCommGroup.forall_mem_range_nsmulAddMonoidHom_pow_prod_iff
    fun _ ↦ PadicInt.eq_zero_of_forall_mem_range_nsmul_pow).mp fun n ↦ ?_
  obtain ⟨z, hz⟩ := Subgroup.mem_iInf.mp hy n
  exact ⟨z.toAdd, by rw [← hz]; rfl⟩

end Prime

variable {F : Type*} [Field F] [Algebra ℚ_[2] F] {f : F[X]} [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]

/-- **The size of `J(F) / 2 J(F)` over a `2`-adic field**: `2 ^ (g d) * #J(F)[2]`, with
`d = [F : ℚ_[2]]`. -/
theorem card_modPow_two (L : LocalStructure 2 F f g) :
    Nat.card (HypJac F f ⧸ (powMonoidHom 2 : HypJac F f →* HypJac F f).range) =
      2 ^ (g * finrank ℚ_[2] F) * Nat.card (powMonoidHom 2 : HypJac F f →* HypJac F f).ker := by
  rw [L.card_modPow_two_eq, PadicInt.index_range_nsmul_self, mul_comm g]

theorem mem_iInf_range_powMonoidHom_two_pow_iff (L : LocalStructure 2 F f g) {x : HypJac F f} :
    x ∈ ⨅ n : ℕ, (powMonoidHom (2 ^ n) : HypJac F f →* HypJac F f).range ↔ Odd (orderOf x) := by
  rw [L.mem_iInf_range_powMonoidHom_pow_iff, Nat.coprime_two_right]

end HypJac.LocalStructure

/-- **Reduction of torsion** for the Jacobian `J` of `y ^ 2 = F(x)` with `F ∈ ℤ[X]`: a
homomorphism from `J(ℚ)` to `J̃(𝔽_p)`, the Jacobian of `y ^ 2 = F̄(x)` for the reduction `F̄` of `F`
modulo `p`, that is injective on the elements of finite order. Reduction modulo `p` is such a
homomorphism when `F` is monic of odd degree and squarefree and `p ≥ 3` is a prime not dividing
the discriminant of `F`, that is, with `F̄` squarefree: its kernel is torsion-free, as the
ramification index `1` of `ℚ_[p]` is less than `p - 1`. Cited, not proved: N. M. Katz, *Galois
properties of torsion points on abelian varieties*, Invent. Math. 62 (1981), 481–502, Appendix;
for the torsion of order prime to `p` also M. Hindry and J. H. Silverman, *Diophantine geometry.
An introduction*, GTM 201, Springer, 2000, Theorem C.1.4 on p. 263. The structure does not define
the reduction map; it asserts only that such a homomorphism exists. -/
structure HypJac.TorsionReduction (p : ℕ) [Fact p.Prime] (F : ℤ[X])
    [Fact (Odd (F.map (Int.castRingHom ℚ)).natDegree)]
    [Fact (Odd (F.map (Int.castRingHom (ZMod p))).natDegree)] : Prop where
  /-- A homomorphism `J(ℚ) → J̃(𝔽_p)` injective on the elements of finite order, in the form: an
  element of finite order in its kernel is trivial (equivalent, as the elements of finite order
  form a subgroup). -/
  exists_monoidHom : ∃ r : HypJac ℚ (F.map (Int.castRingHom ℚ)) →*
      HypJac (ZMod p) (F.map (Int.castRingHom (ZMod p))), ∀ x, IsOfFinOrder x → r x = 1 → x = 1

namespace HypJac.TorsionReduction

variable {p : ℕ} [Fact p.Prime] {F : ℤ[X]} [Fact (Odd (F.map (Int.castRingHom ℚ)).natDegree)]
  [Fact (Odd (F.map (Int.castRingHom (ZMod p))).natDegree)]

/-- If every element `y` of `J̃(𝔽_p)` satisfies `y ^ m = 1`, then so does every element of finite
order of `J(ℚ)`. The polynomials `f` over `ℚ` and `g` over `ZMod p` are any ones equal to the
images of `F`, so that the statement applies to the curves in the form in which they are given. -/
theorem pow_eq_one_of_isOfFinOrder (h : TorsionReduction p F) {f : ℚ[X]} {g : (ZMod p)[X]}
    [Fact (Odd f.natDegree)] [Fact (Odd g.natDegree)] (hf : F.map (Int.castRingHom ℚ) = f)
    (hg : F.map (Int.castRingHom (ZMod p)) = g) {m : ℕ} (hm : ∀ y : HypJac (ZMod p) g, y ^ m = 1)
    {x : HypJac ℚ f} (hx : IsOfFinOrder x) : x ^ m = 1 := by
  subst hf hg
  obtain ⟨r, hr⟩ := h.exists_monoidHom
  exact hr _ hx.pow (by rw [map_pow, hm])

end HypJac.TorsionReduction

end ChabautyColeman

end
