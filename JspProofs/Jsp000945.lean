/-
Copyright (c) 2026 xinkuangsi-spec. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: xinkuangsi-spec
-/
import Mathlib

/-!
# JSP-000945 · An integer all of whose differences from twice smaller squares are prime

The catalog problem asks (Erdős Problem #1140, [Va99, 1.6] and
[EpGi10, MoWi89]): does there exist an integer `n` such that `n - 2x²`
is prime for every `x` with `2x² < n`?

The answer is yes. The known such `n` are

    2, 5, 7, 13, 31, 61, 181, 199,

and results of Epure–Gica (with Mollin–Williams) show these are, with at
most one exception, all of them (in particular the set is finite — the
full classification needs real-quadratic-field machinery far beyond the
scope of this file).

We verify the property for the largest known witness `n = 199`: the
relevant `x` satisfy `x ≤ 9`, and the ten differences

    199, 197, 191, 181, 167, 149, 127, 101, 71, 37

are all prime.  The same finite check is recorded for every other known
value, giving the complete list of known witnesses.
-/

/-- The property: `n − 2x²` is prime whenever `2x² < n`. -/
def Jsp945Good (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime

/-- If `2x² < n ≤ 199` then `x < 10`. -/
private lemma x_lt_ten {n x : ℕ} (hn : n ≤ 199) (h : 2 * x ^ 2 < n) : x < 10 := by
  by_contra hx
  push Not at hx
  have h1 : 10 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
  omega

/-- `199` works: `199 − 2x² ∈ {199,197,191,181,167,149,127,101,71,37}`. -/
theorem good_199 : Jsp945Good 199 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (le_refl 199) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- `2` works (only `x = 0` is permitted, and `2` is prime). -/
theorem good_2 : Jsp945Good 2 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (by norm_num) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- `5` works: `5 − 2x² ∈ {5, 3}`. -/
theorem good_5 : Jsp945Good 5 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (by norm_num) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- `7` works: `7 − 2x² ∈ {7, 5}`. -/
theorem good_7 : Jsp945Good 7 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (by norm_num) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- `13` works: `13 − 2x² ∈ {13, 11, 5}`. -/
theorem good_13 : Jsp945Good 13 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (by norm_num) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- `31` works: `31 − 2x² ∈ {31, 29, 23, 13}`. -/
theorem good_31 : Jsp945Good 31 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (by norm_num) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- `61` works: `61 − 2x² ∈ {61, 59, 53, 43, 29, 11}`. -/
theorem good_61 : Jsp945Good 61 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (by norm_num) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- `181` works: `181 − 2x² ∈ {181,179,173,163,149,131,109,83,53,19}`. -/
theorem good_181 : Jsp945Good 181 := by
  intro x hlt
  have hx : x < 10 := x_lt_ten (by norm_num) hlt
  interval_cases x <;> first | (norm_num at hlt; done) | norm_num

/-- Every element of the known list `{2,5,7,13,31,61,181,199}` has the
property. -/
theorem jsp_000945_known_values :
    ∀ n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Finset ℕ), Jsp945Good n := by
  intro n hn
  fin_cases hn <;>
    first
      | exact good_2 | exact good_5 | exact good_7 | exact good_13
      | exact good_31 | exact good_61 | exact good_181 | exact good_199

/-- The stated existence question of JSP-000945 has a positive answer:
`n = 199` is an integer all of whose differences `n − 2x²` (with
`2x² < n`) are prime. -/
theorem jsp_000945_answer :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → (n - 2 * x ^ 2).Prime :=
  ⟨199, by norm_num, good_199⟩
