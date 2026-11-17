/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.Torsion

-- Beyond the sibling, for the proof of `AddCommGroup.forall_mem_range_nsmulAddMonoidHom_pow_iff`
-- only: Krull's intersection theorem (`Mathlib.RingTheory.Filtration`) and the instance
-- `IsNoetherianRing ℤ` (`Mathlib.RingTheory.PrincipalIdealDomain`), which the sibling does not
-- import; for the proofs of `MonoidHom.coprime_orderOf_of_mem_iInf_range_powMonoidHom_pow` and
-- `Subgroup.coprime_orderOf_mk_of_mem_iInf_sup_range_powMonoidHom_pow` only, the mirrors of
-- `Mathlib.Algebra.Group.Subgroup.Ker` (`MonoidHom.map_range_powMonoidHom_le` and
-- `range_powMonoidHom_le_of_dvd`) and of `Mathlib.Algebra.Group.Subgroup.Pointwise`
-- (`Subgroup.sup_iInf_eq_of_directed`).
import HyperellipticCurves.Mathlib.Algebra.Group.Subgroup.Ker
import HyperellipticCurves.Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Elements that are `p ^ n`-th powers for every `n`

In a finitely generated commutative group, the elements that are `p ^ n`-th powers for every `n`
are those of order prime to `p`. If `H` is a finite subgroup of a commutative group `G` in which
the elements that are `p ^ n`-th powers for every `n` have order prime to `p`, then every element
of `G` that lies in `H ⊔ (powMonoidHom (p ^ n)).range` for every `n` has an image of order prime
to `p` in `G ⧸ H`.

## Main statements

* `CommGroup.mem_range_powMonoidHom_of_coprime`: an element of order prime to `n` is an `n`-th
  power.
* `CommGroup.forall_mem_range_powMonoidHom_pow_iff`: in a finitely generated commutative group, an
  element is a `p ^ n`-th power for every `n` if and only if its order is prime to `p`.
* `CommGroup.forall_mem_range_powMonoidHom_pow_prod_iff`: the same for `A × T` with `T` finite and
  `1` the only element of `A` that is a `p ^ n`-th power for every `n`.
* `MonoidHom.coprime_orderOf_of_mem_iInf_range_powMonoidHom_pow`: for an injective `f : M →* N`,
  if the elements of `N` that are `p ^ n`-th powers for every `n` have order prime to `p`, then so
  have those of `M`.
* `Subgroup.coprime_orderOf_mk_of_mem_iInf_sup_range_powMonoidHom_pow`: if `H` is finite and the
  elements of `G` that are `p ^ n`-th powers for every `n` have order prime to `p`, the image in
  `G ⧸ H` of every element of this intersection has order prime to `p`.

## Implementation notes

The proof of `CommGroup.forall_mem_range_powMonoidHom_pow_iff` goes through `ℤ`-modules: it uses
Krull's intersection theorem `Ideal.mem_iInf_smul_pow_eq_bot_iff` for the ideal `p ℤ`. So the
additive version `AddCommGroup.forall_mem_range_nsmulAddMonoidHom_pow_iff` is proved first, and the
multiplicative one is deduced through `Additive`. Upstream, this result and the ones depending on
it need a file that imports `Mathlib.RingTheory.Filtration`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

open CommGroup

/-! ### Elements divisible by all powers of `p` -/

namespace CommGroup

variable {G : Type*} [CommGroup G]

/-- The form of `exists_pow_eq_self_of_coprime` for the subgroup of `n`-th powers. -/
@[to_additive /-- The form of `exists_nsmul_eq_self_of_coprime` for the subgroup of `n`-fold
multiples. -/]
theorem mem_range_powMonoidHom_of_coprime {n : ℕ} {g : G} (h : (orderOf g).Coprime n) :
    g ∈ (powMonoidHom n).range :=
  let ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h.symm
  ⟨g ^ m, (pow_right_comm g m n).trans hm⟩

end CommGroup

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G]

/-- In a finitely generated abelian group, the elements divisible by every power of `p` are those
of order prime to `p`, by the **Krull intersection theorem** for the ideal `p ℤ`. For `p ≠ 1`, these
elements have finite order, since `Nat.Coprime 0 p` means `p = 1`. -/
theorem forall_mem_range_nsmulAddMonoidHom_pow_iff [IsAddFG G] {p : ℕ} {g : G} :
    (∀ n : ℕ, g ∈ (nsmulAddMonoidHom (p ^ n)).range) ↔ (addOrderOf g).Coprime p := by
  refine ⟨fun h ↦ ?_, fun h n ↦ mem_range_nsmulAddMonoidHom_of_coprime (h.pow_right n)⟩
  let I := Ideal.span {(p : ℤ)}
  have hg : g ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule ℤ G) := by
    refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    obtain ⟨y, rfl⟩ := h n
    exact ⟨y, trivial, by simp [← natCast_zsmul]⟩
  obtain ⟨⟨r, hr⟩, hrg⟩ := (I.mem_iInf_smul_pow_eq_bot_iff g).mp hg
  obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hd : (addOrderOf g : ℤ) ∣ 1 - k * p :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr (by rw [sub_smul, one_smul, hrg, sub_self])
  exact Nat.isCoprime_iff_coprime.mp <|
    (IsCoprime.sub_mul_right_left_iff.mpr isCoprime_one_left).of_isCoprime_of_dvd_left hd

end AddCommGroup

namespace CommGroup

variable {G : Type*} [CommGroup G]

/-- In a finitely generated commutative group, the elements that are `p ^ n`-th powers for every
`n` are those of order prime to `p`. This is deduced from
`AddCommGroup.forall_mem_range_nsmulAddMonoidHom_pow_iff` through `Additive G`, since the proof of
the latter goes through `ℤ`-modules and cannot be translated by `to_additive`. -/
@[to_additive existing forall_mem_range_nsmulAddMonoidHom_pow_iff]
theorem forall_mem_range_powMonoidHom_pow_iff [IsMulFG G] {p : ℕ} {g : G} :
    (∀ n : ℕ, g ∈ (powMonoidHom (p ^ n)).range) ↔ (orderOf g).Coprime p := by
  simpa [← ofMul_pow] using
    AddCommGroup.forall_mem_range_nsmulAddMonoidHom_pow_iff (G := Additive G) (g := .ofMul g)

/-- In `A × T` with `T` finite and `1` the only element of `A` that is a `p ^ n`-th power for
every `n`, the elements that are `p ^ n`-th powers for every `n` are those of finite order prime to
`p`. -/
@[to_additive forall_mem_range_nsmulAddMonoidHom_pow_prod_iff /-- In `A × T` with `T` finite and
`0` the only element of `A` divisible by every power of `p`, the elements divisible by every power
of `p` are those of finite additive order prime to `p`. -/]
theorem forall_mem_range_powMonoidHom_pow_prod_iff {A T : Type*} [CommGroup A] [CommGroup T]
    [Finite T] {p : ℕ}
    (hA : ∀ a : A, (∀ n : ℕ, a ∈ (powMonoidHom (p ^ n) : A →* A).range) → a = 1) {x : A × T} :
    (∀ n : ℕ, x ∈ (powMonoidHom (p ^ n) : A × T →* A × T).range) ↔ (orderOf x).Coprime p := by
  refine ⟨fun h ↦ ?_, fun h n ↦ mem_range_powMonoidHom_of_coprime (h.pow_right n)⟩
  have h1 : x.1 = 1 := hA _ fun n ↦ (h n).elim fun y hy ↦ ⟨y.1, congr(Prod.fst $hy)⟩
  have h2 := (forall_mem_range_powMonoidHom_pow_iff (p := p) (g := x.2)).mp
    fun n ↦ (h n).elim fun y hy ↦ ⟨y.2, congr(Prod.snd $hy)⟩
  rwa [← Prod.mk.eta (p := x), Prod.orderOf_mk, h1, orderOf_one, Nat.lcm_one_left]

end CommGroup

namespace MonoidHom

variable {M N : Type*} [CommGroup M] [CommGroup N]

/-- If `f` is injective and the elements of `N` that are `p ^ n`-th powers for every `n` have
order prime to `p`, then so have those of `M`, since `f` maps such elements to such elements and
preserves orders. -/
@[to_additive coprime_addOrderOf_of_mem_iInf_range_nsmulAddMonoidHom_pow /-- If `f` is injective
and the elements of `N` that are `p ^ n`-fold multiples for every `n` have additive order prime to
`p`, then so have those of `M`, since `f` maps such elements to such elements and preserves
additive orders. -/]
theorem coprime_orderOf_of_mem_iInf_range_powMonoidHom_pow {f : M →* N}
    (hf : Function.Injective f) {p : ℕ}
    (hN : ∀ y ∈ ⨅ n : ℕ, (powMonoidHom (p ^ n) : N →* N).range, (orderOf y).Coprime p) {x : M}
    (hx : x ∈ ⨅ n : ℕ, (powMonoidHom (p ^ n) : M →* M).range) :
    (orderOf x).Coprime p :=
  orderOf_injective f hf x ▸ hN (f x) (Subgroup.mem_iInf.mpr fun n ↦
    f.map_range_powMonoidHom_le _ ⟨x, Subgroup.mem_iInf.mp hx n, rfl⟩)

end MonoidHom

/-! ### The intersection of the subgroups `H ⊔ (powMonoidHom (p ^ n)).range` -/

namespace Subgroup

section Group

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal] {p : ℕ}

/-- The image in `G ⧸ H` of an element of `H ⊔ K` is that of an element of `K`, whose order it
divides. -/
@[to_additive /-- The image in `G ⧸ H` of an element of `H ⊔ K` is that of an element of `K`,
whose additive order it divides. -/]
theorem coprime_orderOf_mk_of_mem_sup {K : Subgroup G} (hK : ∀ x ∈ K, (orderOf x).Coprime p)
    {g : G} (hg : g ∈ H ⊔ K) :
    (orderOf (g : G ⧸ H)).Coprime p := by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_sup_of_normal_left.mp hg
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h).mpr hh, one_mul]
  exact (hK k hk).coprime_dvd_left (orderOf_map_dvd (QuotientGroup.mk' H) k)

end Group

variable {G : Type*} [CommGroup G] {H : Subgroup G} {p : ℕ}

/-- If `H` is finite and every element that is a `p ^ n`-th power for every `n` has order prime to
`p`, then the image in `G ⧸ H` of every element of the intersection of the subgroups
`H ⊔ (powMonoidHom (p ^ n)).range` has order prime to `p`: by `Subgroup.sup_iInf_eq_of_directed`,
the element is the product of an element of `H` and an element of order prime to `p`. -/
@[to_additive coprime_addOrderOf_mk_of_mem_iInf_sup_range_nsmulAddMonoidHom_pow
/-- If `H` is finite and every element that is a `p ^ n`-fold multiple for every `n` has additive
order prime to `p`, then the image in `G ⧸ H` of every element of the intersection of the additive
subgroups `H ⊔ (nsmulAddMonoidHom (p ^ n)).range` has additive order prime to `p`: by
`AddSubgroup.sup_iInf_eq_of_directed`, the element is the sum of an element of `H` and an element
of additive order prime to `p`. -/]
theorem coprime_orderOf_mk_of_mem_iInf_sup_range_powMonoidHom_pow [Finite H]
    (hG : ∀ x ∈ ⨅ n : ℕ, (powMonoidHom (p ^ n) : G →* G).range, (orderOf x).Coprime p) {g : G}
    (hg : g ∈ ⨅ n : ℕ, H ⊔ (powMonoidHom (p ^ n)).range) :
    (orderOf (g : G ⧸ H)).Coprime p :=
  coprime_orderOf_mk_of_mem_sup hG <| (sup_iInf_eq_of_directed <| Antitone.directed_ge
    fun _ _ h ↦ range_powMonoidHom_le_of_dvd (pow_dvd_pow p h)).ge hg

end Subgroup
