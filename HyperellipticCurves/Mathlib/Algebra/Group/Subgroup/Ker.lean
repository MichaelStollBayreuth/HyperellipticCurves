/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

import Mathlib.Data.Int.GCD

/-!
# Kernels and images of subgroups under group homomorphisms

## Main statements

* `MonoidHom.disjoint_ker_iff_injOn`: a homomorphism is injective on a subgroup if and only if the
  subgroup meets its kernel trivially.
* `MonoidHom.le_comap_range_powMonoidHom`, `MonoidHom.map_range_powMonoidHom_le`: a homomorphism
  of commutative groups maps `n`-th powers to `n`-th powers, so that it induces a homomorphism of
  the quotients by the subgroups of `n`-th powers.
* `range_powMonoidHom_le_of_dvd`: if `m ∣ n`, every `n`-th power is an `m`-th power.
* `MonoidHom.range_comp_le_range_powMonoidHom_mul`: if `f` maps into the `p`-th powers and `g`
  into the `q`-th powers, then `f ∘ g` maps into the `p * q`-th powers.
* `Subgroup.map_powMonoidHom_le_range_powMonoidHom_mul`: if `H` consists of `m`-th powers, then the
  `n`-th powers of the elements of `H` are `n * m`-th powers.
* `Subgroup.sup_range_powMonoidHom_pow_eq_top`: if every element is the product of an element
  of `H` and a `p`-th power, then also of an element of `H` and a `p ^ n`-th power.
* `MulEquiv.map_ker_powMonoidHom`: an isomorphism maps the elements of order dividing `n` onto
  the elements of order dividing `n`.

Auxiliary material for the formalization of `2`-descent on hyperelliptic Jacobians;
upstreaming candidates for Mathlib.
-/

@[expose] public section

namespace MonoidHom

section Ker

variable {G N P : Type*} [Group G] [Group N] [MulOneClass P]

@[to_additive]
theorem disjoint_ker_iff_injOn {f : G →* N} {H : Subgroup G} :
    Disjoint H f.ker ↔ Set.InjOn f H := by
  simp [Set.injOn_iff_map_eq_one, Subgroup.disjoint_def]

end Ker

section powMonoidHom

variable {M N : Type*} [CommGroup M] [CommGroup N]

/-- A homomorphism of commutative groups maps `n`-th powers to `n`-th powers. This is the
hypothesis of `QuotientGroup.map` for the homomorphism
`M ⧸ (powMonoidHom n).range →* N ⧸ (powMonoidHom n).range` induced by `f`. -/
@[to_additive /-- A homomorphism of additive commutative groups maps `n`-fold multiples to
`n`-fold multiples. This is the hypothesis of `QuotientAddGroup.map` for the homomorphism
`M ⧸ (nsmulAddMonoidHom n).range →+ N ⧸ (nsmulAddMonoidHom n).range` induced by `f`. -/]
theorem le_comap_range_powMonoidHom (f : M →* N) (n : ℕ) :
    (powMonoidHom n).range ≤ (powMonoidHom n).range.comap f :=
  fun _ ⟨x, hx⟩ ↦ ⟨f x, hx ▸ (map_pow f x n).symm⟩

@[to_additive]
theorem map_range_powMonoidHom_le (f : M →* N) (n : ℕ) :
    (powMonoidHom n).range.map f ≤ (powMonoidHom n).range :=
  Subgroup.map_le_iff_le_comap.mpr (f.le_comap_range_powMonoidHom n)

@[to_additive]
theorem _root_.range_powMonoidHom_le_of_dvd {m n : ℕ} (h : m ∣ n) :
    (powMonoidHom n).range ≤ (powMonoidHom (α := M) m).range := by
  obtain ⟨k, rfl⟩ := h
  exact fun _ ⟨x, hx⟩ ↦ ⟨x ^ k, hx ▸ (pow_mul' x m k).symm⟩

@[to_additive range_comp_le_range_nsmulAddMonoidHom_mul]
theorem range_comp_le_range_powMonoidHom_mul {G : Type*} [Group G] {f : M →* N} {g : G →* M}
    {p q : ℕ} (hf : f.range ≤ (powMonoidHom p).range) (hg : g.range ≤ (powMonoidHom q).range) :
    (f.comp g).range ≤ (powMonoidHom (p * q)).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy : y ^ q = g x⟩ := hg ⟨x, rfl⟩
  obtain ⟨z, hz : z ^ p = f y⟩ := hf ⟨y, rfl⟩
  exact ⟨z, by rw [powMonoidHom_apply, pow_mul, hz, ← map_pow, hy, comp_apply]⟩

end powMonoidHom

end MonoidHom

namespace Subgroup

variable {G N : Type*} [CommGroup G] [CommGroup N]

@[to_additive map_nsmulAddMonoidHom_le_range_nsmulAddMonoidHom_mul]
theorem map_powMonoidHom_le_range_powMonoidHom_mul {H : Subgroup G} {m : ℕ}
    (h : H ≤ (powMonoidHom m).range) (n : ℕ) :
    H.map (powMonoidHom n) ≤ (powMonoidHom (n * m)).range :=
  (map_mono h).trans <| (MonoidHom.map_range ..).trans_le <|
    MonoidHom.range_comp_le_range_powMonoidHom_mul le_rfl le_rfl

/-- If every element is the product of an element of `H` and a `p`-th power, then also of an
element of `H` and a `p ^ n`-th power: the `p`-th power of `γ * y ^ (p ^ n)` is
`γ ^ p * y ^ (p ^ (n + 1))`. -/
theorem sup_range_powMonoidHom_pow_eq_top {H : Subgroup G} {p : ℕ}
    (h : H ⊔ (powMonoidHom p).range = ⊤) (n : ℕ) : H ⊔ (powMonoidHom (p ^ n)).range = ⊤ := by
  induction n with
  | zero => exact eq_top_iff.mpr fun x _ ↦ mem_sup_right ⟨x, pow_one x⟩
  | succ n ih =>
    refine eq_top_iff.mpr (h ▸ sup_le le_sup_left ?_)
    rw [MonoidHom.range_eq_map, ← ih, map_sup, pow_succ']
    exact sup_le_sup (map_le_iff_le_comap.mpr fun x hx ↦ pow_mem hx p)
      (map_powMonoidHom_le_range_powMonoidHom_mul le_rfl p)

end Subgroup

namespace MulEquiv

variable {M N : Type*} [CommGroup M] [CommGroup N]

/-- An isomorphism of commutative groups maps the elements of order dividing `n` onto the
elements of order dividing `n`; compare `MulEquiv.map_range_powMonoidHom`. -/
@[to_additive /-- An isomorphism of additive commutative groups maps the kernel of multiplication
by `n` onto the kernel of multiplication by `n`; compare `AddEquiv.map_range_nsmulAddMonoidHom`. -/]
theorem map_ker_powMonoidHom (e : M ≃* N) (n : ℕ) :
    (powMonoidHom (α := M) n).ker.map e = (powMonoidHom (α := N) n).ker := by
  ext x
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun hx ↦ ⟨e.symm x, ?_, e.apply_symm_apply x⟩⟩
  · subst hyx
    simp_all [← map_pow]
  · simp_all [← map_pow]

end MulEquiv
