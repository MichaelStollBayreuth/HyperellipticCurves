/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Squarefree elements and square divisibility

`Squarefree.dvd_of_sq_dvd_mul_sq`: in a unique factorization monoid, `n² ∣ f · b²` with
`f` squarefree implies `n ∣ b`. The proof is by induction on the prime factors of `n` and
avoids `normalizedFactors` (so no `NormalizationMonoid` instance is required — none exists
e.g. for `K[X]` over a bare field `K`).

Its only client is the general conjugate-ideal norm identity
(`HyperellipticCurves.Archive.ConjugateIdealNorm`), which is why the file sits in the archive; the
statement is a Mathlib gap in its own right.
-/

@[expose] public section

variable {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

-- The inductive crux: a prime `p` with `(p·n)² ∣ f·b²` and `f` squarefree divides `b`
-- (else `p²` would divide `f`).
private lemma prime_dvd_of_sq_mul_dvd {f b p n : α} (hf : Squarefree f) (hp : Prime p)
    (h : (p * n) ^ 2 ∣ f * b ^ 2) : p ∣ b := by
  by_contra hpb
  have hpn2 : (p * n) ^ 2 = p ^ 2 * n ^ 2 := mul_pow p n 2
  have hpfb : p ∣ f * b ^ 2 :=
    ((dvd_mul_right p n).trans (dvd_pow_self (p * n) two_ne_zero)).trans h
  have hpf : p ∣ f := by
    rcases hp.dvd_mul.mp hpfb with h1 | h1
    · exact h1
    · exact absurd (hp.dvd_of_dvd_pow h1) hpb
  obtain ⟨f', rfl⟩ := hpf
  have hp2 : p * p ∣ p * (f' * b ^ 2) := by
    calc p * p = p ^ 2 := (sq p).symm
      _ ∣ (p * n) ^ 2 := by rw [hpn2]; exact dvd_mul_right _ _
      _ ∣ p * f' * b ^ 2 := h
      _ = p * (f' * b ^ 2) := by rw [mul_assoc]
  have hpf' : p ∣ f' * b ^ 2 := (mul_dvd_mul_iff_left hp.ne_zero).mp hp2
  have hdvd : p ∣ f' := by
    rcases hp.dvd_mul.mp hpf' with h1 | h1
    · exact h1
    · exact absurd (hp.dvd_of_dvd_pow h1) hpb
  obtain ⟨f'', rfl⟩ := hdvd
  exact hp.not_isUnit (hf p ⟨f'', by rw [mul_assoc]⟩)

/-- In a unique factorization monoid, if `n² ∣ f · b²` with `f` squarefree, then `n ∣ b`. -/
theorem Squarefree.dvd_of_sq_dvd_mul_sq {f n b : α} (hf : Squarefree f) (h : n ^ 2 ∣ f * b ^ 2) :
    n ∣ b := by
  induction n using UniqueFactorizationMonoid.induction_on_prime generalizing b with
  | h₁ =>
    rcases eq_or_ne b 0 with rfl | hb
    · exact dvd_zero 0
    rcases eq_or_ne f 0 with rfl | hf0
    · exact (hf 0 (dvd_zero _)).dvd
    rw [zero_pow two_ne_zero, zero_dvd_iff] at h
    exact absurd h (mul_ne_zero hf0 (pow_ne_zero 2 hb))
  | h₂ n hn => exact hn.dvd
  | h₃ n p hn hp ih =>
    obtain ⟨b', rfl⟩ := prime_dvd_of_sq_mul_dvd hf hp h
    have h' : n ^ 2 ∣ f * b' ^ 2 := by
      have hpn2 : (p * n) ^ 2 = p ^ 2 * n ^ 2 := mul_pow p n 2
      have h2 : p ^ 2 * n ^ 2 ∣ p ^ 2 * (f * b' ^ 2) := by
        rw [← hpn2]
        calc (p * n) ^ 2 ∣ f * (p * b') ^ 2 := h
          _ = p ^ 2 * (f * b' ^ 2) := by rw [mul_pow, mul_left_comm]
      exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hp.ne_zero)).mp h2
    exact mul_dvd_mul_left p (ih h')

end
