import Mathlib

/-!
# Erdős Problem #389: the examples `n = 2, k = 5` and `n = 3, k = 4`

Erdős asked whether for every `n ≥ 1` there is a `k` with
`n(n+1)⋯(n+k−1) ∣ (n+k)⋯(n+2k−1)` (OPEN; not addressed here).  The problem page records:
"For example when `n = 2` we have `k = 5`: `2·3·4·5·6 ∣ 7·8·9·10·11`, and when `n = 3` we have
`k = 4`: `3·4·5·6 ∣ 7·8·9·10`."  This file verifies these two examples, in the shape used by the
formal-conjectures file for #389 (`∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k,
(n + k + i)`), and also that `5` and `4` are the least such `k` (as in the formal-conjectures
`IsLeast` statement for `n = 4`, and as recorded in OEIS A375071 cited by the page), by
kernel-checked computation without `native_decide`.  The general question and the other
computed values are not claimed.
-/

/-- The `n = 2`, `k = 5` product on the left: `2·3·4·5·6 = 720`. -/
theorem prod_range_five_two : ∏ i ∈ Finset.range 5, (2 + i) = 720 := by
  simp [Finset.prod_range_succ]

/-- **Erdős #389, the `n = 2` example**: `k = 5` is the least `k ≥ 1` with
`2·3·4·5·6 ∣ 7·8·9·10·11`. -/
theorem erdos_389_two_five :
    IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (2 + i) ∣ ∏ i ∈ Finset.range k, (2 + k + i)} 5 := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    norm_num [Finset.prod_range_succ]
  · rintro k ⟨hk1, hk⟩
    by_contra hlt
    rw [Nat.not_le] at hlt
    interval_cases k <;> norm_num [Finset.prod_range_succ] at hk

/-- **Erdős #389, the `n = 3` example**: `k = 4` is the least `k ≥ 1` with `3·4·5·6 ∣ 7·8·9·10`. -/
theorem erdos_389_three_four :
    IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (3 + i) ∣ ∏ i ∈ Finset.range k, (3 + k + i)} 4 := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    norm_num [Finset.prod_range_succ]
  · rintro k ⟨hk1, hk⟩
    by_contra hlt
    rw [Nat.not_le] at hlt
    interval_cases k <;> norm_num [Finset.prod_range_succ] at hk

/-- Both examples as one closed statement, used as the graded root. -/
theorem erdos_389_examples_closed :
    IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (2 + i) ∣ ∏ i ∈ Finset.range k, (2 + k + i)} 5 ∧
    IsLeast {k | 1 ≤ k ∧ ∏ i ∈ Finset.range k, (3 + i) ∣ ∏ i ∈ Finset.range k, (3 + k + i)} 4 :=
  ⟨erdos_389_two_five, erdos_389_three_four⟩
