/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import HyperellipticCurves.Curve.MumfordClass

/-!
# Certificates for exact halving on odd-degree hyperelliptic Jacobians

Let `K` be a field in which `2 ≠ 0` and `f : K[X]` a squarefree polynomial of odd degree, and
write `[u, v]` for the class `ChabautyColeman.mumfordClass f u v` of the Mumford ideal `(u, y - v)`
in the Jacobian `HypJac K f` of the curve `y ^ 2 = f`. For a point `[a, b]` that is twice another
point, Proposition 5.1 of [Sto17] computes a half `[w, r]` from the solution of a system of linear
congruences. This file turns the output of that computation into a certificate: a short list of
polynomial identities and divisibilities that implies `[a, b] = 2 [w, r]` and can be checked by
polynomial arithmetic, so that neither the linear algebra nor the square root of the proposition
has to be trusted. When the first polynomial `A` of a point `[A, B]` is not squarefree, a
halving algorithm forms the half as a sum, by Cantor's algorithm; a second certificate turns a run
of Cantor's algorithm into a proof of the sum, so that a halving record certifies the half in its
reduced Mumford representation.

## Main definitions

* `ChabautyColeman.HalvingCertificate`: a certificate for `[a, b] = 2 [w, r]` in the generic case
  of [Sto17], Proposition 5.1: the function `u * y - v` of its proof, a constant `lam` with
  `v ^ 2 - u ^ 2 * f = lam * a * w ^ 2`, and Bézout cofactors for `u` and `a * w ^ 2`.
* `ChabautyColeman.AdditionCertificate`: a certificate for `[u₁, v₁] + [u₂, v₂] = [u, v]` in the
  form of a run of Cantor's algorithm: a common factor that cancels, the composed pair, and a
  chain of reduction steps.
* `ChabautyColeman.HalvingData`: a halving record for a point `[A, B]` with
  `A = a0 ^ 2 * a`: a halving certificate for a twist of the pair `(a, b)`, the factors that relate
  its half to the half `[w, r]` of `[a, b]`, and an addition certificate for
  `[a0, B] + [w, r] = [UH, VH]`.

## Main statements

* `ChabautyColeman.HalvingCertificate.mumfordClass_eq_sq`: a halving certificate shows
  `[a, b] = 2 [w, r]`.
* `ChabautyColeman.HalvingCertificate.dvd_sq_sub`,
  `ChabautyColeman.HalvingCertificate.dvd_sq_sub_half`: `(a, b)` and `(w, r)` are Mumford pairs;
  the other lemmas in the namespace `ChabautyColeman.HalvingCertificate` are the congruences on
  which the proof rests.
* `ChabautyColeman.mumfordClass_eq_sq_of_halvingCertificate`: [Sto17], Proposition 5.1, in general:
  a halving certificate for a twist of `(a, b)` shows `[a, b] = 2 [w, r]`.
* `ChabautyColeman.AdditionCertificate.mumfordClass_mul_mumfordClass`: an addition certificate shows
  `[u₁, v₁] + [u₂, v₂] = [u, v]`.
* `ChabautyColeman.HalvingData.mumfordClass_eq_sq`: a halving record shows `[A, B] = 2 [UH, VH]`.

## Implementation notes

The Jacobian `HypJac K f` is a multiplicative group, so `[a, b] = 2 [w, r]` reads
`mumfordClass f a b = mumfordClass f w r ^ 2`. The certificate is a structure because its data
come from a computation and each condition is checked separately; the same holds for the addition
certificate and the record. They need only `[Field K]`, and they have no monicity, degree or
squarefreeness conditions: these matter for the existence of a certificate and for reading a class
`[u, v]` as the point with the Mumford representation `(u, v)`, but not for the identities. The
constant `lam` is `(-c) ^ (deg a)` for the leading coefficient `c` of `f` in [Sto17]; the
statements hold for every `lam ≠ 0`. The chain of reduction steps of an addition certificate
consists of sequences `ℕ → K[X]` and `ℕ → K` with one hypothesis `∀ i < n, …` for each condition.

## References

* [Sto17] M. Stoll, *Chabauty without the Mordell-Weil group*, 2017, Section 5
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K]

/-! ### The certificate in the generic case -/

/-- A certificate that the class of `(a, b)` is twice the class of `(w, r)`
(`ChabautyColeman.HalvingCertificate.mumfordClass_eq_sq`), following the proof of [Sto17],
Proposition 5.1: the function `u * y - v` has norm `lam * a * w ^ 2`, `v ≡ u * b` modulo `a`,
`u * r ≡ -v` modulo `w`, and `u` is coprime to `a * w ^ 2`. -/
structure HalvingCertificate (f a b w r : K[X]) where
  /-- The coefficient of `y` in the function `u y - v`. -/
  u : K[X]
  /-- The constant term of the function `u y - v`. -/
  v : K[X]
  /-- The Bézout cofactor of `u`: `e * u + e' * (a * w ^ 2) = 1`. -/
  e : K[X]
  /-- The Bézout cofactor of `a * w ^ 2`. -/
  e' : K[X]
  /-- The constant of the norm identity `v ^ 2 - u ^ 2 * f = C lam * (a * w ^ 2)`. -/
  lam : K
  /-- The constant of the norm identity is nonzero. -/
  lam_ne_zero : lam ≠ 0
  /-- The norm of `u y - v` is `lam` times `a * w ^ 2`. -/
  sq_sub_eq : v ^ 2 - u ^ 2 * f = C lam * (a * w ^ 2)
  /-- `v ≡ u * b` modulo `a`. -/
  dvd_sub_mul : a ∣ v - u * b
  /-- `u * r ≡ -v` modulo `w`. -/
  dvd_mul_add : w ∣ u * r + v
  /-- The Bézout identity for `u` and `a * w ^ 2`. -/
  mul_add_mul_eq_one : e * u + e' * (a * w ^ 2) = 1

namespace HalvingCertificate

variable {f a b w r : K[X]} (h : HalvingCertificate f a b w r)
include h

theorem dvd_mul_sub_one : a * w ^ 2 ∣ h.e * h.u - 1 :=
  ⟨-h.e', by linear_combination h.mul_add_mul_eq_one⟩

theorem dvd_mul_sq_sub : a * w ^ 2 ∣ (h.e * h.v) ^ 2 - f :=
  dvd_mul_sq_sub_of_dvd_sq_sub_sq_mul (Dvd.intro_left _ h.sq_sub_eq.symm) h.dvd_mul_sub_one

theorem dvd_mul_sub : a ∣ h.e * h.v - b :=
  (dvd_add (h.dvd_sub_mul.mul_left h.e)
    ((dvd_of_mul_right_dvd h.dvd_mul_sub_one).mul_right b)).trans (dvd_of_eq (by ring))

/-- The counterpart of `ChabautyColeman.HalvingCertificate.dvd_mul_sub` for the half `(w, r)`:
`e * v ≡ -r` modulo `w`. -/
theorem dvd_mul_add_half : w ∣ h.e * h.v + r :=
  (dvd_sub (h.dvd_mul_add.mul_left h.e)
    ((((dvd_pow_self w two_ne_zero).mul_left a).trans h.dvd_mul_sub_one).mul_right r)).trans
    (dvd_of_eq (by ring))

theorem dvd_sq_sub : a ∣ b ^ 2 - f :=
  (dvd_sq_sub_iff_of_dvd_sub h.dvd_mul_sub).mp ((dvd_mul_right a _).trans h.dvd_mul_sq_sub)

/-- The counterpart of `ChabautyColeman.HalvingCertificate.dvd_sq_sub` for the half: `(w, r)` is a
Mumford pair. -/
theorem dvd_sq_sub_half : w ∣ r ^ 2 - f :=
  (dvd_sq_sub_iff_of_dvd_add h.dvd_mul_add_half).mp
    (((dvd_pow_self w two_ne_zero).mul_left a).trans h.dvd_mul_sq_sub)

/-- **[Sto17], Proposition 5.1**, generic case, in certificate form: the class of
`(a * w ^ 2, e * v)` is trivial (`ChabautyColeman.mumfordClass_eq_one_of_sq_sub_eq`), and it is
the class of `(a, b)` plus twice the class of `(w, -r)`. -/
theorem mumfordClass_eq_sq [Fact (Odd f.natDegree)] [NeZero (2 : K)] [Fact (Squarefree f)] :
    mumfordClass f a b = mumfordClass f w r ^ 2 := by
  have hw2 : w ^ 2 ∣ (h.e * h.v) ^ 2 - f := (dvd_mul_left _ a).trans h.dvd_mul_sq_sub
  have hprin := mumfordClass_eq_one_of_sq_sub_eq f h.lam_ne_zero h.sq_sub_eq h.dvd_mul_sub_one
  rw [mumfordClass_mul f h.dvd_mul_sq_sub, mumfordClass_pow f hw2,
    mumfordClass_eq_of_dvd_sub f h.dvd_mul_sub] at hprin
  rw [mumfordClass_eq_inv_of_dvd_add f ((dvd_pow_self w two_ne_zero).trans hw2)
    h.dvd_mul_add_half, inv_pow]
  exact eq_inv_of_mul_eq_one_left hprin

end HalvingCertificate

/-! ### The general case -/

/-- **[Sto17], Proposition 5.1**, in certificate form, in general: a halving certificate for
`(a, Bt)` with half `(W, R)`, where `Bt ≡ b` modulo `a'` and `Bt ≡ -b` modulo `da` for
`a = a' * da`, shows that the class of `(a, b)` is twice the class of `(w, r)` for
`w = df * da * W` with `r ≡ 0` modulo `df`, `r ≡ b` modulo `da` and `r ≡ R` modulo `W`. Neither `a'`
and `da` nor the three factors of `w` need to be coprime. -/
theorem mumfordClass_eq_sq_of_halvingCertificate {f : K[X]} [Fact (Odd f.natDegree)]
    [NeZero (2 : K)] [Fact (Squarefree f)] {a b w r a' da df Bt W R : K[X]}
    (hab : a ∣ b ^ 2 - f) (ha : a = a' * da) (hBt₁ : a' ∣ Bt - b) (hBt₂ : da ∣ Bt + b)
    (hw : w = df * da * W) (hwr : w ∣ r ^ 2 - f) (hdf : df ∣ r) (hda : da ∣ r - b)
    (hW : W ∣ r - R) (h : HalvingCertificate f a Bt W R) :
    mumfordClass f a b = mumfordClass f w r ^ 2 := by
  subst ha hw
  rw [mumfordClass_mul_eq_mul_sq f hab hBt₁ hBt₂, h.mumfordClass_eq_sq, mumfordClass_mul f hwr,
    mumfordClass_eq_of_dvd_sub f hW,
    mumfordClass_mul_of_dvd_sub f (v₁ := 0) (dvd_of_mul_right_dvd hwr) (by simpa) hda, mul_pow,
    mul_pow, mumfordClass_zero_sq f ((dvd_sub_right (hdf.pow two_ne_zero)).mp
      ((dvd_mul_of_dvd_left (dvd_mul_right df da) W).trans hwr)), one_mul, mul_comm]

/-! ### Cantor's algorithm in certificate form -/

/-- A certificate that the sum of the classes of the Mumford pairs `(u₁, v₁)` and `(u₂, v₂)` is
the class of `(u, v)` (`ChabautyColeman.AdditionCertificate.mumfordClass_mul_mumfordClass`), in the
form of a run of Cantor's algorithm: the common factor `t` of `u₁` and `u₂` on which the two pairs
are opposite, the composed pair `(u' 0, v' 0)` with `u' 0 = p₁ * p₂`, and `n` reduction steps
from it to `(u' n, v' n) = (u, v)`. Only the values of `u'` and `v'` at `0, …, n` and those of
`lam` at `0, …, n - 1` matter. -/
structure AdditionCertificate (f u₁ v₁ u₂ v₂ u v : K[X]) where
  /-- The common factor of `u₁` and `u₂` that cancels. -/
  t : K[X]
  /-- The cofactor of `t` in `u₁`. -/
  p₁ : K[X]
  /-- The cofactor of `t` in `u₂`. -/
  p₂ : K[X]
  /-- The number of reduction steps. -/
  n : ℕ
  /-- The first polynomials of the pairs of the chain, from the composed pair to the sum. -/
  u' : ℕ → K[X]
  /-- The second polynomials of the pairs of the chain. -/
  v' : ℕ → K[X]
  /-- The constants of the reduction steps: `v' i ^ 2 - f = C (lam i) * (u' i * u' (i + 1))`. -/
  lam : ℕ → K
  /-- `t` divides `u₁`, with cofactor `p₁`. -/
  eq_mul_left : u₁ = t * p₁
  /-- `t` divides `u₂`, with cofactor `p₂`. -/
  eq_mul_right : u₂ = t * p₂
  /-- The two pairs are opposite on `t`: `v₂ ≡ -v₁` modulo `t`. -/
  dvd_add' : t ∣ v₁ + v₂
  /-- The first polynomial of the composed pair is `p₁ * p₂`. -/
  u'_zero : u' 0 = p₁ * p₂
  /-- The composed pair is a Mumford pair. -/
  dvd_sq_sub : u' 0 ∣ v' 0 ^ 2 - f
  /-- `v' 0 ≡ v₁` modulo `p₁`. -/
  dvd_sub_left' : p₁ ∣ v' 0 - v₁
  /-- `v' 0 ≡ v₂` modulo `p₂`. -/
  dvd_sub_right' : p₂ ∣ v' 0 - v₂
  /-- The reduction steps: the norm of `y - v' i` is `lam i * u' i * u' (i + 1)`. -/
  sq_sub_eq : ∀ i < n, v' i ^ 2 - f = C (lam i) * (u' i * u' (i + 1))
  /-- The reduction steps: `v' (i + 1) ≡ -v' i` modulo `u' (i + 1)`. -/
  dvd_add_succ : ∀ i < n, u' (i + 1) ∣ v' i + v' (i + 1)
  /-- The chain ends in the first polynomial `u` of the sum. -/
  u'_n : u' n = u
  /-- The chain ends in the second polynomial `v` of the sum. -/
  v'_n : v' n = v

/-- **Cantor's algorithm**, in certificate form: an addition certificate for two Mumford pairs
with sum `(u, v)` shows that the sum of their classes is the class of `(u, v)`. The certificate
needs no Bézout cofactors for the composition, allows a common factor `t`, and puts no condition on
degrees or leading coefficients, so it does not show that `(u, v)` is reduced. -/
theorem AdditionCertificate.mumfordClass_mul_mumfordClass {f u₁ v₁ u₂ v₂ u v : K[X]}
    [Fact (Odd f.natDegree)] [NeZero (2 : K)] [Fact (Squarefree f)]
    (h : AdditionCertificate f u₁ v₁ u₂ v₂ u v) (h₁ : u₁ ∣ v₁ ^ 2 - f) (h₂ : u₂ ∣ v₂ ^ 2 - f) :
    mumfordClass f u₁ v₁ * mumfordClass f u₂ v₂ = mumfordClass f u v := by
  rw [congr(mumfordClass f $(h.eq_mul_left) v₁ * mumfordClass f $(h.eq_mul_right) v₂),
    mumfordClass_mul_mumfordClass_eq_of_dvd_add f (h.eq_mul_left ▸ h₁) (h.eq_mul_right ▸ h₂)
      h.dvd_add',
    ← mumfordClass_mul_of_dvd_sub f (h.u'_zero ▸ h.dvd_sq_sub) h.dvd_sub_left' h.dvd_sub_right',
    ← h.u'_zero, mumfordClass_eq_of_forall_sq_sub_eq f h.sq_sub_eq h.dvd_add_succ, h.u'_n, h.v'_n]

/-! ### Halving records -/

/-- A halving record: a certificate that `(UH, VH)`, the Mumford pair of a half computed by the
algorithm of [Sto17], Proposition 5.1, is a half of `(A, B)`. -/
structure HalvingData (f A B UH VH : K[X]) where
  /-- The square factor of `A`: `A = a0 ^ 2 * a`. -/
  a0 : K[X]
  /-- The squarefree part of `A`. -/
  a : K[X]
  /-- A representative of `B` modulo `a`. -/
  b : K[X]
  /-- The cofactor `a / da`. -/
  aq : K[X]
  /-- The factor of `a` on which `Bt ≡ -b`; also a factor of `w`. -/
  da : K[X]
  /-- The factor of `w` on which `r ≡ 0`. -/
  df : K[X]
  /-- The second polynomial of the halving certificate: `Bt ≡ b mod aq`, `Bt ≡ -b mod da`. -/
  Bt : K[X]
  /-- The first polynomial of the half of the halving certificate: `w = df * da * W`. -/
  W : K[X]
  /-- The second polynomial of the half of the halving certificate: `R ≡ r mod W`. -/
  R : K[X]
  /-- The first polynomial of the half `[w, r]` of `[a, b]`. -/
  w : K[X]
  /-- The second polynomial of the half `[w, r]` of `[a, b]`. -/
  r : K[X]
  /-- The halving certificate of `[a, Bt] = 2 [W, R]`. -/
  cert : HalvingCertificate f a Bt W R
  /-- The addition certificate of `[a0, B] + [w, r] = [UH, VH]`. -/
  add : AdditionCertificate f a0 B w r UH VH
  /-- `a0 ^ 2` divides `A`, with cofactor `a`. -/
  eq_sq_mul : A = a0 ^ 2 * a
  /-- `(A, B)` is a Mumford pair. -/
  dvd_sq_sub : A ∣ B ^ 2 - f
  /-- `b ≡ B` modulo `a`. -/
  dvd_sub' : a ∣ b - B
  /-- `da` divides `a`, with cofactor `aq`. -/
  eq_mul : a = aq * da
  /-- `Bt ≡ b` modulo `aq`. -/
  dvd_sub_Bt : aq ∣ Bt - b
  /-- `Bt ≡ -b` modulo `da`. -/
  dvd_add_Bt : da ∣ Bt + b
  /-- The first polynomial `w` of the half is the product `df * da * W`. -/
  eq_mul_mul : w = df * da * W
  /-- `(w, r)` is a Mumford pair. -/
  dvd_sq_sub_half : w ∣ r ^ 2 - f
  /-- `r ≡ 0` modulo `df`. -/
  dvd_r : df ∣ r
  /-- `r ≡ b` modulo `da`. -/
  dvd_r_sub : da ∣ r - b
  /-- `r ≡ R` modulo `W`. -/
  dvd_r_sub_R : W ∣ r - R

/-- A halving record shows that the class of `(A, B)` is twice the class of `(UH, VH)`, the
computed half: by `ChabautyColeman.mumfordClass_sq_mul` and
`ChabautyColeman.mumfordClass_eq_sq_of_halvingCertificate`, the class of `(A, B)` is twice the
sum of the classes of `(a0, B)` and `(w, r)`, and the addition certificate identifies this sum
with the class of `(UH, VH)`. -/
theorem HalvingData.mumfordClass_eq_sq {f : K[X]} [Fact (Odd f.natDegree)] [NeZero (2 : K)]
    [Fact (Squarefree f)] {A B UH VH : K[X]} (h : HalvingData f A B UH VH) :
    mumfordClass f A B = mumfordClass f UH VH ^ 2 := by
  have hA : h.a0 ^ 2 * h.a ∣ B ^ 2 - f := h.eq_sq_mul ▸ h.dvd_sq_sub
  have hab : h.a ∣ h.b ^ 2 - f :=
    (dvd_sq_sub_iff_of_dvd_sub h.dvd_sub').mpr ((dvd_mul_left _ _).trans hA)
  rw [h.eq_sq_mul, mumfordClass_sq_mul f hA,
    mumfordClass_eq_of_dvd_sub f (dvd_sub_comm.mp h.dvd_sub'),
    mumfordClass_eq_sq_of_halvingCertificate hab h.eq_mul h.dvd_sub_Bt h.dvd_add_Bt h.eq_mul_mul
      h.dvd_sq_sub_half h.dvd_r h.dvd_r_sub h.dvd_r_sub_R h.cert, ← mul_pow,
    h.add.mumfordClass_mul_mumfordClass
      ((dvd_pow_self _ two_ne_zero).trans (dvd_of_mul_right_dvd hA)) h.dvd_sq_sub_half]

end ChabautyColeman
