/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import HyperellipticCurves.Mathlib.RingTheory.Polynomial.ChineseRemainder
public import HyperellipticCurves.Mathlib.RingTheory.Valuation.Integral

import HyperellipticCurves.Mathlib.RingTheory.AdjoinRoot
import HyperellipticCurves.Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
import HyperellipticCurves.Mathlib.RingTheory.Norm.AdjoinRoot

/-!
# The group `A(Σ, n)` and the point lemmas

Let `K` be the fraction field of a Dedekind domain `R`, let `f` be a squarefree polynomial over
`K` and let `S` be a set of primes of `R`. The group `A(S, n)` of [Sto17], Section 5, is the
subgroup of `(K[X] ⧸ (f))ˣ / n`-th powers of the classes whose component in each field factor of
`K[X] ⧸ (f)` lies in the Selmer group relative to the primes above `S`. For odd degree and
`n = 2`, the point lemma says that for a point `(x₀, y₀)` on `y ^ 2 = f x` with `y₀ ≠ 0` the
class of `x₀ - θ` lies in `A(S, 2)` when `S` contains the bad primes of `f`: at a good prime the
valuation of `x₀ - θ` is a square, by a case distinction on the integrality of `x₀`. The point
lemma for Mumford polynomials says that for `a ∣ b ^ 2 - f` prime to `f` and a root `θ` of `f` in a
field `L`, the class of `lc(a)⁻¹ * a(θ)` lies in the Selmer group of `L`: by induction on the
irreducible factors of `a`, it is a product of norms of `θ - x` for points `(x, b(x))` over the
fields `L[X] ⧸ (a')`.

## Main definitions

* `AdjoinRoot.selmerGroup`: the group `A(S, n)`.

## Main statements

* `AdjoinRoot.mk_mem_selmerGroup_iff`: the class of a unit lies in `A(S, n)` iff its valuation at
  each prime of each field factor not above `S` is divisible by `n`.
* `AdjoinRoot.finite_selmerGroup`: `A(S, n)` is finite for finite `S` over a number field.
* `AdjoinRoot.mem_selmerGroup_iff_of_splits`: for `f` with distinct roots `α i` in `K`, a class
  lies in `A(S, n)` iff its root coordinates lie in `K⟮S, n⟯`.
* `Valuation.exists_map_sub_eq_sq`: the point lemma for a single valuation.
* `Polynomial.HasSeparableReduction.exists_map_sub_eq_sq`: the point lemma for a polynomial with
  separable reduction.
* `IsDedekindDomain.mem_selmerGroupAbove_of_sq_eq_aeval`: the point lemma in a field.
* `AdjoinRoot.of_sub_root_mem_selmerGroup`: the point lemma, `x₀ - θ` lies in `A(S, 2)`.
* `IsDedekindDomain.mem_selmerGroup_of_dvd_sq_sub`,
  `IsDedekindDomain.mem_selmerGroupAbove_of_dvd_sq_sub`: the point lemma for Mumford polynomials,
  `lc(a)⁻¹ * a(θ)` lies in the Selmer group.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5
-/

@[expose] public section

open Polynomial IsDedekindDomain

namespace AdjoinRoot

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {f : K[X]} [∀ p : f.Factors, Algebra.IsSeparable K (AdjoinRoot (p : K[X]))]

/-- The Selmer group `A(S, n)` of `K[X] ⧸ (f)`, for a squarefree `f` over the fraction
field `K` of a Dedekind domain `R` and a set `S` of primes of `R`: the classes of units of
`K[X] ⧸ (f)` modulo `n`-th powers whose component in each field factor `L_p = K[X] ⧸ (p)`, under
`AdjoinRoot.modPowEquivPiFactors`, lies in the Selmer group of `L_p` relative to the primes of the
integral closure of `R` in `L_p` above `S` (`IsDedekindDomain.selmerGroupAbove`). The factors are
assumed separable over `K` (automatic for a perfect field), so that these integral closures are
Dedekind domains. -/
noncomputable def selmerGroup (hsq : Squarefree f) (S : Set (HeightOneSpectrum R)) (n : ℕ) :
    Subgroup (Units.ModPow (AdjoinRoot f) n) :=
  selmerGroupOfEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X]))
    (fun p ↦ integralClosure R (AdjoinRoot (p : K[X])))
    (fun _ ↦ HeightOneSpectrum.primesAbove R _ S) n (modPowEquivPiFactors hsq n)

theorem mem_selmerGroup_iff (hsq : Squarefree f) (S : Set (HeightOneSpectrum R)) (n : ℕ)
    (x : Units.ModPow (AdjoinRoot f) n) :
    x ∈ selmerGroup hsq S n ↔ ∀ p : f.Factors, modPowEquivPiFactors hsq n x p ∈
      selmerGroupAbove R (integralClosure R (AdjoinRoot (p : K[X]))) (AdjoinRoot (p : K[X])) S n :=
  mem_selmerGroupOfEquiv_iff ..

/-- The class of a unit `u` lies in `AdjoinRoot.selmerGroup` exactly when, for each field factor
`L_p`, the valuation of the image of `u` in `L_p` is divisible by `n` at every prime of the
integral closure of `R` in `L_p` not above `S`. -/
theorem mk_mem_selmerGroup_iff (hsq : Squarefree f) (S : Set (HeightOneSpectrum R)) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) :
    (u : Units.ModPow (AdjoinRoot f) n) ∈ selmerGroup hsq S n ↔ ∀ p : f.Factors,
      ∀ w ∉ HeightOneSpectrum.primesAbove R (integralClosure R (AdjoinRoot (p : K[X]))) S,
        (n : ℤ) ∣ Multiplicative.toAdd
          (w.valuationOfNeZero (Units.map (projFactor hsq p).toMonoidHom u)) := by
  simp only [mem_selmerGroup_iff, modPowEquivPiFactors_mk, mem_selmerGroupAbove_iff,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]

/-- `AdjoinRoot.selmerGroup` is finite if `S` is finite and the integral closure of `R` in each
field factor has a finite class group and finitely generated units (for instance if `K` is a
number field). -/
theorem finite_selmerGroup (hsq : Squarefree f) {S : Set (HeightOneSpectrum R)} (hS : S.Finite)
    (n : ℕ) [NeZero n]
    [∀ p : f.Factors, Finite (ClassGroup (integralClosure R (AdjoinRoot (p : K[X]))))]
    [∀ p : f.Factors, IsMulFG (integralClosure R (AdjoinRoot (p : K[X])))ˣ] :
    Finite (selmerGroup hsq S n) :=
  have := Factors.finite hsq.ne_zero
  finite_selmerGroupOfEquiv _ _ _ n (fun _ ↦ HeightOneSpectrum.primesAbove_finite R _ hS) _

end AdjoinRoot

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- **The point lemma, locally**: let `g` have `v`-integral coefficients, a `v`-unit leading
coefficient and odd degree, let `θ` be a root of `g` at which `g'` is a `v`-unit, and let
`y ^ 2 = g x ≠ 0`. Then `v (x - θ)` is a square. If `x` is not `v`-integral, `v (x - θ) = v x` and
the leading term of `g` dominates; otherwise `Valuation.map_sub_eq_one_or_eq_map_eval` applies. -/
theorem exists_map_sub_eq_sq {g : K[X]} (hlc : v g.leadingCoeff = 1) (hg : ∀ i, v (g.coeff i) ≤ 1)
    (hodd : Odd g.natDegree) {θ x y : K} (hθ : g.eval θ = 0) (hd : v (g.derivative.eval θ) = 1)
    (hy : y ^ 2 = g.eval x) (hy0 : y ≠ 0) :
    ∃ z : Kˣ, v (x - θ) = v (z : K) ^ 2 := by
  have hθ1 := v.le_one_of_eval_eq_zero hlc (fun i _ ↦ hg i) hodd.pos.ne' hθ
  rcases le_or_gt (v x) 1 with hx | hx
  · refine (v.map_sub_eq_one_or_eq_map_eval hg hθ hθ1 hx hd).elim (fun h ↦ ⟨1, by simp [h]⟩)
      fun h ↦ ⟨Units.mk0 y hy0, by rw [h, ← hy, Units.val_mk0, map_pow]⟩
  obtain ⟨k, hk⟩ := hodd
  have hx0 : x ≠ 0 := v.ne_zero_iff.mp (zero_lt_one.trans hx).ne'
  refine ⟨Units.mk0 (y / x ^ k) (div_ne_zero hy0 (pow_ne_zero k hx0)), ?_⟩
  rw [v.map_sub_eq_of_lt_left (hθ1.trans_lt hx), Units.val_mk0, ← map_pow, div_pow, hy, map_div₀,
    v.map_eval_eq_of_one_lt hlc (fun i _ ↦ hg i) hx, hk, ← pow_mul, map_pow, pow_succ,
    mul_comm k 2, mul_div_cancel_left₀ _ (pow_ne_zero _ (v.ne_zero_iff.mpr hx0))]

end Valuation

namespace Polynomial.HasSeparableReduction

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

/-- **The point lemma, locally**, for `g` of odd degree with separable reduction at `v`: if `θ` is
a root of `g` and `y ^ 2 = g x ≠ 0`, then `v (x - θ)` is a square. As `Res(g, g')` is a `v`-unit,
so is `g'` at `θ` (`Valuation.map_derivative_eval_eq_one`), and `Valuation.exists_map_sub_eq_sq`
applies. -/
theorem exists_map_sub_eq_sq {g : K[X]} (h : g.HasSeparableReduction v) (hodd : Odd g.natDegree)
    {θ x y : K} (hθ : g.eval θ = 0) (hy : y ^ 2 = g.eval x) (hy0 : y ≠ 0) :
    ∃ z : Kˣ, v (x - θ) = v (z : K) ^ 2 := by
  refine v.exists_map_sub_eq_sq h.leadingCoeff_eq_one h.coeff_le_one hodd hθ ?_ hy hy0
  exact v.map_derivative_eval_eq_one h.coeff_le_one hθ
    (v.le_one_of_eval_eq_zero h.leadingCoeff_eq_one (fun i _ ↦ h.coeff_le_one i) hodd.pos.ne' hθ)
    hodd.pos.ne' (v.map_resultant_derivative_eq_one (natDegree_pos_iff_degree_pos.mp hodd.pos)
      h.leadingCoeff_eq_one h.discr_eq_one)

end Polynomial.HasSeparableReduction

namespace IsDedekindDomain

section Point

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Algebra.IsIntegral R B] [Module.IsTorsionFree R B] {L : Type*} [Field L] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L]

/-- **The point lemma in a field**: let `f` have odd degree and separable reduction at the
primes of `R` outside `S`. If `θ` is a root of `f` in `L` and `y ^ 2 = f x ≠ 0` in `L`, then the
class of `x - θ` lies in the Selmer group of `L` relative to the primes above `S`: at a prime `w`
of `B` not above `S` the image of `f` in `L[X]` has separable reduction
(`Polynomial.HasSeparableReduction.map`), and
`Polynomial.HasSeparableReduction.exists_map_sub_eq_sq` applies. -/
theorem mem_selmerGroupAbove_of_sq_eq_aeval {f : K[X]} (hodd : Odd f.natDegree)
    {S : Set (HeightOneSpectrum R)} (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K))
    {θ x y : L} (hθ : aeval θ f = 0) (hy : y ^ 2 = aeval x f) (h0 : aeval x f ≠ 0) {u : Lˣ}
    (hu : (u : L) = x - θ) :
    (u : Units.ModPow L 2) ∈ selmerGroupAbove R B L S 2 := by
  refine (mem_selmerGroupAbove_iff R B L S 2 _).mpr fun w hw ↦ ?_
  have hv : w.under R ∉ S := (HeightOneSpectrum.mem_primesAbove_iff ..).not.mp hw
  obtain ⟨z, hz⟩ := ((hS _ hv).map fun _ ↦ w.valuation_algebraMap_le_one L).exists_map_sub_eq_sq
    (by rwa [natDegree_map]) (by rwa [eval_map_algebraMap]) (by rwa [eval_map_algebraMap])
    (by rintro rfl; simp [← hy] at h0)
  exact (w.valuationOfNeZeroMod_mk_eq_one_iff 2 u).mpr
    (w.dvd_toAdd_valuationOfNeZero (z := z) (hu ▸ hz))

end Point

section Norm

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {L : Type*} [Field L] [Algebra B L]
  [IsFractionRing B L] {F : Type*} [Field F] [Algebra L F] [Algebra B F] [IsScalarTower B L F]
  [FiniteDimensional L F] [Algebra.IsSeparable L F]

/-- **The norm of a point**: let `F / L` be a finite separable extension, and let `g` have odd
degree and separable reduction at the primes of `B` outside `T`. If `θ` is a root of `g` in `L` and
`y ^ 2 = g x ≠ 0` in `F`, then the class of `N_{F/L}(θ - x)` lies in `L⟮T, 2⟯`. The class of
`x - θ`, and so that of `θ - x`, lies in the Selmer group of `F` relative to the primes of the
integral closure of `B` above `T` (`IsDedekindDomain.mem_selmerGroupAbove_of_sq_eq_aeval`), which
the norm maps into `L⟮T, 2⟯` (`IsDedekindDomain.norm_mem_selmerGroup`). -/
theorem norm_sub_mem_selmerGroup_of_sq_eq_aeval {T : Set (HeightOneSpectrum B)} {g : L[X]}
    (hodd : Odd g.natDegree) (hT : ∀ v ∉ T, g.HasSeparableReduction (v.valuation L))
    {θ : L} (hθ : g.eval θ = 0) {x y : F} (hy : y ^ 2 = aeval x g) (h0 : aeval x g ≠ 0) {u : Lˣ}
    (hu : (u : L) = Algebra.norm L (algebraMap L F θ - x)) :
    (u : Units.ModPow L 2) ∈ selmerGroup (K := L) (S := T) (n := 2) := by
  have := integralClosure.isDedekindDomain B L F
  have : IsFractionRing (integralClosure B F) F :=
    integralClosure.isFractionRing_of_finite_extension L F
  have := Module.IsTorsionFree.trans_faithfulSMul B L F
  have hθ' : aeval (algebraMap L F θ) g = 0 := by
    rw [aeval_algebraMap_apply, coe_aeval_eq_eval, hθ, map_zero]
  have hne : x - algebraMap L F θ ≠ 0 := sub_ne_zero.mpr fun he ↦ h0 (he ▸ hθ')
  have hF := mem_selmerGroupAbove_of_sq_eq_aeval (B := integralClosure B F) hodd hT hθ' hy h0
    (u := Units.mk0 _ hne) rfl
  obtain rfl : u = Units.map (Algebra.norm L : F →* L) (-Units.mk0 _ hne) :=
    Units.ext (by simp [hu])
  exact norm_mem_selmerGroup (B := integralClosure B F) L ((mk_neg_mem_selmerGroup_iff _).mpr hF)

end Norm

section DvdSqSub

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {L : Type*} [Field L] [Algebra B L]
  [IsFractionRing B L] [PerfectField L]

-- The case of an irreducible `a` in `IsDedekindDomain.mem_selmerGroup_of_dvd_sq_sub`:
-- `lc(a)⁻¹ * a(θ)` is the norm of `θ - x` from `L[X] ⧸ (a)`, `x` the root of `a`, and
-- `y = b(x)` satisfies `y ^ 2 = g x ≠ 0`.
private theorem mem_selmerGroup_of_irreducible_of_dvd_sq_sub {T : Set (HeightOneSpectrum B)}
    {g : L[X]} (hodd : Odd g.natDegree) (hT : ∀ v ∉ T, g.HasSeparableReduction (v.valuation L))
    {θ : L} (hθ : g.eval θ = 0) {a b : L[X]} (hirr : Irreducible a) (h : a ∣ b ^ 2 - g)
    (ha : IsCoprime a g) {u : Lˣ} (hu : (u : L) = a.leadingCoeff⁻¹ * a.eval θ) :
    (u : Units.ModPow L 2) ∈ selmerGroup (K := L) (S := T) (n := 2) := by
  have : Fact (Irreducible a) := ⟨hirr⟩
  have := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hlc0 : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  refine norm_sub_mem_selmerGroup_of_sq_eq_aeval hodd hT hθ (x := AdjoinRoot.root a)
    (y := AdjoinRoot.mk a b)
    (by rwa [AdjoinRoot.aeval_eq, ← map_pow, AdjoinRoot.mk_eq_mk])
    (by rw [AdjoinRoot.aeval_eq]; exact (AdjoinRoot.isUnit_mk_iff.mpr ha.symm).ne_zero) ?_
  rw [hu, inv_mul_eq_iff_eq_mul₀ hlc0, AdjoinRoot.algebraMap_eq]
  exact (AdjoinRoot.leadingCoeff_mul_norm_of_sub_root (isUnit_iff_ne_zero.mpr hlc0) θ).symm

/-- **The point lemma for Mumford polynomials**, over a Dedekind domain `B` with fraction field
`L`: let `g` have odd degree and separable reduction at the primes of `B` outside `T`. For
`a ∣ b ^ 2 - g` prime to `g` and a root `θ` of `g` in `L`, the class of `lc(a)⁻¹ * a(θ)` lies in
the Selmer group `L⟮T, 2⟯`. By induction on the irreducible factors of `a`, as the value is
multiplicative; for irreducible `a` it is the norm of `θ - x` from `L[X] ⧸ (a)`, `x` the root of
`a`, and `IsDedekindDomain.norm_sub_mem_selmerGroup_of_sq_eq_aeval` applies to the point
`(x, b(x))`. -/
theorem mem_selmerGroup_of_dvd_sq_sub {T : Set (HeightOneSpectrum B)} {g : L[X]}
    (hodd : Odd g.natDegree) (hT : ∀ v ∉ T, g.HasSeparableReduction (v.valuation L))
    {θ : L} (hθ : g.eval θ = 0) {a b : L[X]} (h : a ∣ b ^ 2 - g) (ha : IsCoprime a g) {u : Lˣ}
    (hu : (u : L) = a.leadingCoeff⁻¹ * a.eval θ) :
    (u : Units.ModPow L 2) ∈ selmerGroup (K := L) (S := T) (n := 2) := by
  induction a using WfDvdMonoid.induction_on_irreducible generalizing u with
  | zero => exact absurd (isCoprime_zero_left.mp ha) (not_isUnit_of_natDegree_pos _ hodd.pos)
  | unit c hc =>
    obtain ⟨c, hc0, rfl⟩ := Polynomial.isUnit_iff.mp hc
    obtain rfl : u = 1 := Units.ext (by simp [hu, hc0.ne_zero])
    exact Subgroup.one_mem _
  | mul a i ha0 hi ih =>
    have hne (q : L[X]) (hq0 : q ≠ 0) (hq : IsCoprime q g) : q.leadingCoeff⁻¹ * q.eval θ ≠ 0 := by
      simpa [hq0, hθ] using aeval_ne_zero_of_isCoprime hq θ
    obtain rfl : u = Units.mk0 _ (hne i hi.ne_zero ha.of_mul_left_left) *
        Units.mk0 _ (hne a ha0 ha.of_mul_left_right) :=
      Units.ext (by simp [hu, leadingCoeff_mul]; ring)
    exact mul_mem (mem_selmerGroup_of_irreducible_of_dvd_sq_sub hodd hT hθ hi
      ((dvd_mul_right i a).trans h) ha.of_mul_left_left rfl)
      (ih ((dvd_mul_left a i).trans h) ha.of_mul_left_right rfl)

end DvdSqSub

section Above

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Algebra.IsIntegral R B] [Module.IsTorsionFree R B] {L : Type*} [Field L] [Algebra B L]
  [IsFractionRing B L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L]

/-- The class of the image of `c : K` in `L` lies in the Selmer group of `L` relative to the primes
above `S` if `c` is a unit at every prime of `R` outside `S`. -/
theorem mem_selmerGroupAbove_of_valuation_eq_one {S : Set (HeightOneSpectrum R)} {n : ℕ} {c : K}
    (hc : ∀ v ∉ S, v.valuation K c = 1) {u : Lˣ} (hu : (u : L) = algebraMap K L c) :
    (u : Units.ModPow L n) ∈ selmerGroupAbove R B L S n := by
  refine (mem_selmerGroupAbove_iff R B L S n _).mpr fun w hw ↦ ?_
  have hv : w.under R ∉ S := (HeightOneSpectrum.mem_primesAbove_iff ..).not.mp hw
  refine (w.valuationOfNeZeroMod_mk_eq_one_iff n u).mpr (w.dvd_toAdd_valuationOfNeZero (z := 1) ?_)
  rw [hu, w.valuation_algebraMap_eq_one L (hc _ hv), Units.val_one, map_one, one_pow]

/-- **The point lemma for Mumford polynomials** (blueprint `lem:ds-point-mumford`): let `f` have odd
degree and separable reduction at the primes of `R` outside `S`. For a root `θ` of `f` in `L` and
`a ∣ b ^ 2 - f` prime to `f` in `L[X]`, the class of `lc(a)⁻¹ * a(θ)` lies in the Selmer group of
`L` relative to the primes above `S`: `IsDedekindDomain.mem_selmerGroup_of_dvd_sq_sub` for the image
of `f` in `L[X]`, which has separable reduction at the primes of `B` not above `S`
(`Polynomial.HasSeparableReduction.map`). -/
theorem mem_selmerGroupAbove_of_dvd_sq_sub [PerfectField L] {f : K[X]} (hodd : Odd f.natDegree)
    {S : Set (HeightOneSpectrum R)} (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K))
    {θ : L} (hθ : aeval θ f = 0) {a b : L[X]} (h : a ∣ b ^ 2 - f.map (algebraMap K L))
    (ha : IsCoprime a (f.map (algebraMap K L))) {u : Lˣ}
    (hu : (u : L) = a.leadingCoeff⁻¹ * a.eval θ) :
    (u : Units.ModPow L 2) ∈ selmerGroupAbove R B L S 2 := by
  exact mem_selmerGroup_of_dvd_sq_sub (by rwa [natDegree_map])
    (fun w hw ↦ (hS _ ((HeightOneSpectrum.mem_primesAbove_iff ..).not.mp hw)).map
      fun _ ↦ w.valuation_algebraMap_le_one L)
    (by rwa [eval_map_algebraMap]) h ha hu

end Above

end IsDedekindDomain

namespace AdjoinRoot

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {f : K[X]} [∀ p : f.Factors, Algebra.IsSeparable K (AdjoinRoot (p : K[X]))]

/-- **The point lemma**: let `f` have odd degree and separable reduction at the primes of `R`
outside `S`. If `y₀ ^ 2 = f x₀ ≠ 0`, then the class of `x₀ - θ`, a unit of `K[X] ⧸ (f)` by
`AdjoinRoot.isUnit_of_sub_root`, lies in `AdjoinRoot.selmerGroup`: in each field factor it is
`IsDedekindDomain.mem_selmerGroupAbove_of_sq_eq_aeval`. -/
theorem of_sub_root_mem_selmerGroup (hsq : Squarefree f) (hodd : Odd f.natDegree)
    {S : Set (HeightOneSpectrum R)} (hS : ∀ v ∉ S, f.HasSeparableReduction (v.valuation K))
    {x₀ y₀ : K} (hy : y₀ ^ 2 = f.eval x₀) (h0 : f.eval x₀ ≠ 0) {u : (AdjoinRoot f)ˣ}
    (hu : (u : AdjoinRoot f) = of f x₀ - root f) :
    (u : Units.ModPow (AdjoinRoot f) 2) ∈ selmerGroup hsq S 2 := by
  refine (mem_selmerGroup_iff hsq S 2 _).mpr fun p ↦ ?_
  rw [modPowEquivPiFactors_mk]
  refine mem_selmerGroupAbove_of_sq_eq_aeval hodd hS (θ := root (p : K[X]))
    (x := algebraMap K _ x₀) (y := algebraMap K _ y₀)
    (by rw [aeval_eq, mk_eq_zero]; exact p.dvd)
    (by rw [aeval_algebraMap_apply, coe_aeval_eq_eval, ← hy, map_pow])
    (by rwa [aeval_algebraMap_apply, coe_aeval_eq_eval, _root_.map_ne_zero]) ?_
  simp [hu, algebraMap_eq]

/-- The condition of `AdjoinRoot.selmerGroup` at a linear factor `X - C a` of `f`: the component
lies in the Selmer group of the factor `K[X] ⧸ (X - C a) ≅ K` exactly when the evaluation at `a`
lies in `K⟮S, n⟯` (`IsDedekindDomain.map_algebraMap_mem_selmerGroupAbove_iff` for degree `1`). -/
theorem modPowEquivPiFactors_ofRoot_mem_selmerGroupAbove_iff (hsq : Squarefree f) {a : K}
    (ha : f.IsRoot a) (S : Set (HeightOneSpectrum R)) (n : ℕ)
    (x : Units.ModPow (AdjoinRoot f) n) :
    modPowEquivPiFactors hsq n x (Factors.ofRoot ha) ∈
        selmerGroupAbove R (integralClosure R (AdjoinRoot (Factors.ofRoot ha : K[X])))
          (AdjoinRoot (Factors.ofRoot ha : K[X])) S n ↔
      Units.ModPow.map (liftAlgHom f (Algebra.ofId K K) a (by simpa using ha)) n x ∈
        IsDedekindDomain.selmerGroup (R := R) (K := K) (S := S) (n := n) := by
  rw [modPowEquivPiFactors_ofRoot]
  refine map_algebraMap_mem_selmerGroupAbove_iff ?_
  rw [(powerBasis (Factors.ne_zero _)).finrank, powerBasis_dim, Factors.coe_ofRoot,
    natDegree_X_sub_C]
  exact Nat.coprime_one_left n

/-- **`A(S, n)` for split `f`** (blueprint `lem:ds-e1-selmer` (2)): if `f` has distinct roots `α i`
in `K`, at least `natDegree f` many, a class lies in `AdjoinRoot.selmerGroup` exactly when each of
its root coordinates lies in `K⟮S, n⟯`. The field factors are the `K[X] ⧸ (X - C (α i))`
(`Polynomial.Factors.equivOfRoots`). -/
theorem mem_selmerGroup_iff_of_splits (hsq : Squarefree f) {ι : Type*} [Fintype ι] {α : ι → K}
    (hinj : Function.Injective α) (hroot : ∀ i, f.IsRoot (α i))
    (hcard : f.natDegree ≤ Fintype.card ι) (S : Set (HeightOneSpectrum R)) (n : ℕ)
    (x : Units.ModPow (AdjoinRoot f) n) :
    x ∈ selmerGroup hsq S n ↔ ∀ i,
      Units.ModPow.map (liftAlgHom f (Algebra.ofId K K) (α i) (by simpa using hroot i)) n x ∈
        IsDedekindDomain.selmerGroup (R := R) (K := K) (S := S) (n := n) := by
  rw [mem_selmerGroup_iff]
  exact (Factors.equivOfRoots hsq.ne_zero hinj hroot hcard).forall_congr_right.symm.trans
    (forall_congr' fun i ↦ modPowEquivPiFactors_ofRoot_mem_selmerGroupAbove_iff hsq (hroot i) S n x)

end AdjoinRoot
