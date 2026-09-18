/-
Copyright (c) 2026 xinkuangsi-spec. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: xinkuangsi-spec
-/
import Mathlib

/-!
# JSP-000884 · Comparing `φ(n)` with `φ(n − φ(n))`

The catalog problem asks (Erdős Problem #1064, Guy's B42): how does the
totient `φ(n)` compare with `φ(n − φ(n))`?

The complete answer has two parts:

* `φ(n) > φ(n − φ(n))` for *almost all* `n` — proved by Luca and
  Pomerance [LuPo02] (in fact `φ(n) > φ(n − φ(n)) + f(n)` for any
  `f = o(n)`).  This is a theorem of analytic number theory and is **not**
  formalized here.
* `φ(n) < φ(n − φ(n))` for *infinitely many* `n` — proved by Grytczuk,
  Luca and Wójtowicz [GLW01].  The verification is elementary: already
  `n = 15·2^k` works, since then `φ(n) = 8·2^k` while
  `n − φ(n) = 11·2^{k+1}` and `φ(n − φ(n)) = 10·2^k`.

This file formalizes the qualitative part of the comparison: **each**
of the three relations `<`, `=`, `>` between `φ(n)` and `φ(n − φ(n))`
occurs for infinitely many `n`.  The three explicit families are

* `n = 2^{k+2}`:  `φ(n) = 2^{k+1}`, `n − φ(n) = 2^{k+1}`,
  `φ(n − φ(n)) = 2^k`, so `φ(n) > φ(n − φ(n))`;
* `n = 3·2^{k+1}`: `φ(n) = 2^{k+1}`, `n − φ(n) = 2^{k+2}`,
  `φ(n − φ(n)) = 2^{k+1}`, so `φ(n) = φ(n − φ(n))`;
* `n = 15·2^{k+1}`: `φ(n) = 8·2^k`, `n − φ(n) = 11·2^{k+1}`,
  `φ(n − φ(n)) = 10·2^k`, so `φ(n) < φ(n − φ(n))`.
-/


/-- `φ(2^{j+1}) = 2^j`. -/
private lemma totient_two_pow_succ (j : ℕ) :
    Nat.totient (2 ^ (j + 1)) = 2 ^ j := by
  rw [Nat.totient_prime_pow_succ Nat.prime_two]
  ring

/-- `2^(k+2) = 4·2^k`. -/
private lemma pow_two_add_two (k : ℕ) : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by
  rw [pow_succ', pow_succ']
  ring

/-- Infinitely many `n` satisfy `φ(n) > φ(n − φ(n))` (witnesses `n = 2^{k+2}`). -/
theorem phi_gt_totient_sub_infinite :
    {n : ℕ | Nat.totient n > Nat.totient (n - Nat.totient n)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 2 ^ (k + 2))
  · intro a b hab
    have h := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hab
    omega
  · intro k
    have hφn : Nat.totient (2 ^ (k + 2)) = 2 ^ (k + 1) :=
      totient_two_pow_succ (k + 1)
    have hsub : 2 ^ (k + 2) - 2 ^ (k + 1) = 2 ^ (k + 1) := by
      have h1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' ..
      have h2 := pow_two_add_two k
      omega
    show Nat.totient (2 ^ (k + 2)) > Nat.totient (2 ^ (k + 2) - Nat.totient (2 ^ (k + 2)))
    rw [hφn, hsub, totient_two_pow_succ k]
    have hpk : (0 : ℕ) < 2 ^ k := by positivity
    have h1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' ..
    omega

/-- Infinitely many `n` satisfy `φ(n) = φ(n − φ(n))` (witnesses `n = 3·2^{k+1}`). -/
theorem phi_eq_totient_sub_infinite :
    {n : ℕ | Nat.totient n = Nat.totient (n - Nat.totient n)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 3 * 2 ^ (k + 1))
  · intro a b hab
    have h2 : 2 ^ (a + 1) = 2 ^ (b + 1) := Nat.mul_left_cancel (by norm_num) hab
    have h := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    omega
  · intro k
    have hφ3 : Nat.totient 3 = 2 := by decide
    have hcop : Nat.Coprime 3 (2 ^ (k + 1)) := (by decide : Nat.Coprime 3 2).pow_right _
    have hφn : Nat.totient (3 * 2 ^ (k + 1)) = 2 ^ (k + 1) := by
      rw [Nat.totient_mul hcop, hφ3, Nat.totient_prime_pow_succ Nat.prime_two]
      ring
    have hsub : 3 * 2 ^ (k + 1) - 2 ^ (k + 1) = 2 ^ (k + 2) := by
      have h1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' ..
      have h2 := pow_two_add_two k
      omega
    show Nat.totient (3 * 2 ^ (k + 1)) = Nat.totient (3 * 2 ^ (k + 1) - Nat.totient (3 * 2 ^ (k + 1)))
    rw [hφn, hsub, totient_two_pow_succ (k + 1)]

/-- Infinitely many `n` satisfy `φ(n) < φ(n − φ(n))` (witnesses `n = 15·2^{k+1}`,
the Grytczuk–Luca–Wójtowicz family). -/
theorem phi_lt_totient_sub_infinite :
    {n : ℕ | Nat.totient n < Nat.totient (n - Nat.totient n)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 15 * 2 ^ (k + 1))
  · intro a b hab
    have h2 : 2 ^ (a + 1) = 2 ^ (b + 1) := Nat.mul_left_cancel (by norm_num) hab
    have h := Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    omega
  · intro k
    have hφ15 : Nat.totient 15 = 8 := by decide
    have hφ11 : Nat.totient 11 = 10 := by decide
    have hcop15 : Nat.Coprime 15 (2 ^ (k + 1)) := (by decide : Nat.Coprime 15 2).pow_right _
    have hcop11 : Nat.Coprime 11 (2 ^ (k + 1)) := (by decide : Nat.Coprime 11 2).pow_right _
    have hφn : Nat.totient (15 * 2 ^ (k + 1)) = 8 * 2 ^ k := by
      rw [Nat.totient_mul hcop15, hφ15, Nat.totient_prime_pow_succ Nat.prime_two]
      ring
    have hsub : 15 * 2 ^ (k + 1) - 8 * 2 ^ k = 11 * 2 ^ (k + 1) := by
      have h1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' ..
      omega
    show Nat.totient (15 * 2 ^ (k + 1)) <
      Nat.totient (15 * 2 ^ (k + 1) - Nat.totient (15 * 2 ^ (k + 1)))
    rw [hφn, hsub, Nat.totient_mul hcop11, hφ11, totient_two_pow_succ k]
    have hpk : (0 : ℕ) < 2 ^ k := by positivity
    nlinarith

/-- The qualitative answer to the comparison question of JSP-000884:
each of the three possible comparisons between `φ(n)` and `φ(n − φ(n))`
holds for infinitely many `n`.  (The quantitative strengthening —
`φ(n) > φ(n − φ(n))` on a set of density one — is the Luca–Pomerance
theorem and lies outside the scope of this file.) -/
theorem jsp_000884_answer :
    {n : ℕ | Nat.totient n < Nat.totient (n - Nat.totient n)}.Infinite ∧
    {n : ℕ | Nat.totient n = Nat.totient (n - Nat.totient n)}.Infinite ∧
    {n : ℕ | Nat.totient n > Nat.totient (n - Nat.totient n)}.Infinite :=
  ⟨phi_lt_totient_sub_infinite, phi_eq_totient_sub_infinite, phi_gt_totient_sub_infinite⟩
