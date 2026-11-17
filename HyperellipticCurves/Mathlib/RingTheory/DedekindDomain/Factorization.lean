/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Beyond the sibling: `ClassGroup` and `toPrincipalIdeal`, for `FractionalIdeal.nthRootClass`.
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# `n`-th roots of fractional ideals and the `n`-th-root class map

Let `R` be a Dedekind domain with fraction field `K`. A nonzero fractional ideal is determined by
its valuations `FractionalIdeal.count`, and every tuple of valuations of finite support occurs.
So the fractional ideals all of whose valuations are divisible by `n` have `n`-th roots, and the
`n`-th root is a group homomorphism on them. For a unit `u : Kˣ` whose principal ideal `(u)` is
`n`-divisible, the class of the `n`-th root of `(u)` vanishes exactly when `u` is a unit of `R`
times an `n`-th power: this is exactness in the middle of `1 → Rˣ/(Rˣ)ⁿ → K(∅, n) → Cl(R)[n]`,
before any quotient is taken.

## Main definitions

* `FractionalIdeal.nthRootHom`: the `n`-th root, on the `n`-divisible fractional ideals.
* `FractionalIdeal.unitsNDivisible`: the units of `K` whose principal ideal is `n`-divisible.
* `FractionalIdeal.nthRootClass`: the class of the `n`-th root of `(u)`, for such `u`.

## Main statements

* `FractionalIdeal.count_injective`: a nonzero fractional ideal is determined by its valuations.
* `FractionalIdeal.nthRootHom_pow`: the `n`-th root is an `n`-th root.
* `FractionalIdeal.nthRootClass_eq_one_iff`: the class of the `n`-th root of `(u)` is trivial
  exactly when `u` is a unit of `R` times an `n`-th power.
* `IsDedekindDomain.HeightOneSpectrum.multiplicity_asIdeal_mul`: the multiplicity of a prime in a
  product of nonzero ideals is the sum of the multiplicities.

## Implementation notes

`FractionalIdeal.spanSingleton_eq_one_iff` belongs in
`Mathlib.RingTheory.FractionalIdeal.Operations`, `FractionalIdeal.toPrincipalIdeal_eq_one_iff` and
`ClassGroup.mk_eq_one_iff_exists` in `Mathlib.RingTheory.ClassGroup.Basic`; they are kept here
with their only user.

Vendored from EllipticCurves (`EllipticCurves/Mathlib/FractionalIdeal.lean`), for the finiteness
of Selmer groups; upstreaming candidates for Mathlib.
-/

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal

section PrincipalIdeal

variable [IsDomain R]

theorem spanSingleton_eq_one_iff {x : K} :
    spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R K a = x := by
  rw [← map_one (spanSingleton (P := K) R⁰), eq_comm, spanSingleton_eq_spanSingleton]
  simp [Units.smul_def, Algebra.smul_def]

/-- The principal fractional ideal `(u)` is trivial exactly when `u` comes from a unit of `R`:
the kernel of `toPrincipalIdeal` is the image of `Rˣ`. -/
theorem toPrincipalIdeal_eq_one_iff (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  simp [Units.ext_iff, spanSingleton_eq_one_iff]

/-- `ClassGroup.mk I = 1` exactly when the unit fractional ideal `I` is principal, with the
generator given as a unit of `K`; a variant of `ClassGroup.mk_eq_one_iff` without
`Submodule.IsPrincipal`. -/
theorem _root_.ClassGroup.mk_eq_one_iff_exists {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff, isPrincipal_iff, ← MonoidHom.mem_range, mem_principal_ideals_iff]
  exact exists_congr fun _ ↦ eq_comm

end PrincipalIdeal

variable [IsDedekindDomain R]

/-- The prime `v` as a unit of the group of fractional ideals. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] theorem coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal :=
  rfl

/-- The finitely supported tuple of valuations of a unit fractional ideal. -/
noncomputable def toFinsupp (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count K v (I : FractionalIdeal R⁰ K)) (by
    have := finite_factors (I : FractionalIdeal R⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] theorem toFinsupp_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count K v (I : FractionalIdeal R⁰ K) :=
  rfl

/-- The unit fractional ideal `∏ v ^ (g v)`. -/
noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  g.prod fun v e ↦ unitOfPrime v ^ e

theorem coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      g.prod fun v e ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ e := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom]

theorem count_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count K v ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]

/-- A unit fractional ideal is determined by its valuations. -/
theorem count_injective {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal R⁰ K) = count K v (J : FractionalIdeal R⁰ K)) :
    I = J := by
  apply Units.ext
  rw [← finprod_heightOneSpectrum_factorization' K (Units.ne_zero I),
    ← finprod_heightOneSpectrum_factorization' K (Units.ne_zero J)]
  exact finprod_congr fun v ↦ by rw [h v]

section NthRoot

variable (R K)

/-- The subgroup of fractional ideals whose valuations are all divisible by `n`. -/
def nDivisible (n : ℕ) : Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {I | ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)}
  one_mem' v := by rw [Units.val_one, count_one]; exact dvd_zero _
  mul_mem' {I J} hI hJ v := by
    rw [Units.val_mul, count_mul K v (Units.ne_zero I) (Units.ne_zero J)]
    exact dvd_add (hI v) (hJ v)
  inv_mem' {I} hI v := by
    rw [Units.val_inv_eq_inv_val, count_inv]
    exact (hI v).neg_right

variable {R K} in
theorem mem_nDivisible {n : ℕ} {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ nDivisible R K n ↔ ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K) :=
  Iff.rfl

/-- The fractional ideal whose valuations are those of `I` divided by `n`; an `n`-th root of `I`
if `I` is `n`-divisible (`FractionalIdeal.nthRootHom_pow`). -/
noncomputable def nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) : (FractionalIdeal R⁰ K)ˣ :=
  ofFinsupp (Finsupp.mapRange (· / (n : ℤ)) (by simp) (toFinsupp I))

theorem count_nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    count K v (nthRootFun R K n I : FractionalIdeal R⁰ K) =
      count K v (I : FractionalIdeal R⁰ K) / n := by
  rw [nthRootFun, count_ofFinsupp, Finsupp.mapRange_apply, toFinsupp_apply]

/-- The `n`-th root as a group homomorphism on the `n`-divisible fractional ideals. -/
noncomputable def nthRootHom (n : ℕ) : nDivisible R K n →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ)
  map_one' := count_injective fun v ↦ by
    simp only [count_nthRootFun, Subgroup.coe_one, Units.val_one, count_one, Int.zero_ediv]
  map_mul' I J := count_injective fun v ↦ by
    rw [count_nthRootFun, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      count_nthRootFun, count_nthRootFun, Subgroup.coe_mul, Units.val_mul,
      count_mul K v (Units.ne_zero _) (Units.ne_zero _), Int.add_ediv_of_dvd_left (I.2 v)]

variable {R K} in
@[simp] theorem nthRootHom_apply (n : ℕ) (I : nDivisible R K n) :
    nthRootHom R K n I = nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ) :=
  rfl

theorem nthRootHom_pow (n : ℕ) (I : nDivisible R K n) :
    nthRootHom R K n I ^ n = (I : (FractionalIdeal R⁰ K)ˣ) :=
  count_injective fun v ↦ by
    rw [Units.val_pow_eq_pow_val, count_pow, nthRootHom_apply, count_nthRootFun,
      Int.mul_ediv_cancel' (I.2 v)]

end NthRoot

section NthRootClass

variable (R K)

/-- The units of `K` whose principal fractional ideal has all valuations divisible by `n`. -/
def unitsNDivisible (n : ℕ) : Subgroup Kˣ :=
  (nDivisible R K n).comap (toPrincipalIdeal R K)

variable {R K} in
theorem mem_unitsNDivisible {n : ℕ} {u : Kˣ} :
    u ∈ unitsNDivisible R K n ↔ ∀ v, (n : ℤ) ∣ count K v (spanSingleton R⁰ (u : K)) := by
  rw [unitsNDivisible, Subgroup.mem_comap, mem_nDivisible]
  simp only [coe_toPrincipalIdeal]

/-- The restriction of `toPrincipalIdeal` to `FractionalIdeal.unitsNDivisible`, into the
`n`-divisible fractional ideals. -/
def unitsNDivisibleToNDivisible (n : ℕ) : unitsNDivisible R K n →* nDivisible R K n :=
  (toPrincipalIdeal R K).restrict fun _ hx ↦ hx

@[simp] theorem coe_unitsNDivisibleToNDivisible (n : ℕ) (u : unitsNDivisible R K n) :
    (unitsNDivisibleToNDivisible R K n u : (FractionalIdeal R⁰ K)ˣ) =
      toPrincipalIdeal R K (u : Kˣ) :=
  rfl

/-- The `n`-th-root class map: the class of the `n`-th root of the principal ideal `(u)`. -/
noncomputable def nthRootClass (n : ℕ) : unitsNDivisible R K n →* ClassGroup R :=
  (ClassGroup.mk K).comp ((nthRootHom R K n).comp (unitsNDivisibleToNDivisible R K n))

@[simp]
theorem nthRootClass_apply (n : ℕ) (u : unitsNDivisible R K n) :
    nthRootClass R K n u =
      ClassGroup.mk K (nthRootHom R K n (unitsNDivisibleToNDivisible R K n u)) :=
  rfl

/-- **Exactness of the fundamental sequence in the middle**, before taking quotients: the
`n`-th-root class of `u` vanishes exactly when `u` is a unit of `R` times an `n`-th power. -/
theorem nthRootClass_eq_one_iff {n : ℕ} (hn : n ≠ 0) (u : unitsNDivisible R K n) :
    nthRootClass R K n u = 1 ↔
      ∃ (a : Rˣ) (w : Kˣ), Units.map (algebraMap R K : R →* K) a * w ^ n = (u : Kˣ) := by
  rw [nthRootClass_apply, ClassGroup.mk_eq_one_iff_exists]
  refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun ⟨a, w, hw⟩ ↦ ⟨w, count_injective fun v ↦ ?_⟩⟩
  · -- `wⁿ` generates `(u)`, so `u / wⁿ` is a unit of `R`
    have hpow : toPrincipalIdeal R K (w ^ n) = toPrincipalIdeal R K (u : Kˣ) := by
      rw [map_pow, hw, nthRootHom_pow, coe_unitsNDivisibleToNDivisible]
    have h1 : toPrincipalIdeal R K ((u : Kˣ) * (w ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, hpow, mul_inv_cancel]
    obtain ⟨a, ha⟩ := (toPrincipalIdeal_eq_one_iff _).mp h1
    exact ⟨a, w, by rw [ha]; group⟩
  · -- `w` generates the `n`-th root: its valuations are `count (u) / n`
    have hcu : count K v ((toPrincipalIdeal R K (u : Kˣ) : (FractionalIdeal R⁰ K)ˣ) :
        FractionalIdeal R⁰ K) = n * count K v
          ((toPrincipalIdeal R K w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) := by
      rw [← hw, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
        count_mul K v (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)), count_pow,
        (toPrincipalIdeal_eq_one_iff _).mpr ⟨a, rfl⟩, Units.val_one, count_one, zero_add]
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcu,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hn)]

end NthRootClass

end FractionalIdeal

namespace IsDedekindDomain.HeightOneSpectrum

variable [IsDedekindDomain R]

theorem asIdeal_dvd_asIdeal_iff {v w : HeightOneSpectrum R} : v.asIdeal ∣ w.asIdeal ↔ v = w := by
  rw [Ideal.dvd_iff_le]
  exact ⟨fun h ↦ HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top h).symm,
    fun h ↦ h ▸ le_rfl⟩

theorem multiplicity_asIdeal_of_ne {v w : HeightOneSpectrum R} (h : v ≠ w) :
    multiplicity v.asIdeal w.asIdeal = 0 :=
  multiplicity_eq_zero_of_not_dvd (asIdeal_dvd_asIdeal_iff.not.mpr h)

theorem multiplicity_asIdeal_mul (v : HeightOneSpectrum R) {I J : Ideal R} (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) :
    multiplicity v.asIdeal (I * J) = multiplicity v.asIdeal I + multiplicity v.asIdeal J :=
  multiplicity_mul v.prime (.of_prime_left v.prime (mul_ne_zero hI hJ))

end IsDedekindDomain.HeightOneSpectrum
