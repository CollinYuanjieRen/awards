import Mathlib

/-!
# Erdős Problem 196: every permutation of `ℕ` contains a monotone 3-term arithmetic progression

Davis, Entringer, Graham and Simmons (1977) proved that every permutation `x` of `ℕ` has indices
`i < j < k` such that `x i, x j, x k` form an arithmetic progression.  Proof: let `m = x 0` and let
`p = x⁻¹` give positions.  For `d ≥ 1` the values `m + d` and `m + 2d` sit at positive positions
`p (m + d)` and `p (m + 2d)`.  If `p (m + d) < p (m + 2d)` for some `d`, the indices
`0 < p (m + d) < p (m + 2d)` carry the progression `m, m + d, m + 2d`.  Otherwise
`p (m + 2d) < p (m + d)` for every `d ≥ 1`, so `p (m + 2 ^ (j + 1)) < p (m + 2 ^ j)` for all `j`,
an infinite strictly decreasing sequence of natural numbers, which is impossible.
-/

namespace Erdos196

/-- `x` has a monotone 3-term arithmetic progression: indices `i < j < k` whose values are in
arithmetic progression (`x i + x k = 2 x j`, increasing or decreasing). -/
def HasMonotoneAP3 (x : ℕ ≃ ℕ) : Prop := ∃ i j k : ℕ, i < j ∧ j < k ∧ x i + x k = 2 * x j

/-- The progression found in the proof is increasing: `x i < x j < x k`. -/
def HasIncreasingAP3 (x : ℕ ≃ ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ x i < x j ∧ x j < x k ∧ x i + x k = 2 * x j

theorem HasIncreasingAP3.hasMonotoneAP3 {x : ℕ ≃ ℕ} (h : HasIncreasingAP3 x) : HasMonotoneAP3 x := by
  obtain ⟨i, j, k, hij, hjk, -, -, h⟩ := h
  exact ⟨i, j, k, hij, hjk, h⟩

/-- **Davis–Entringer–Graham–Simmons (1977).** Every permutation of `ℕ` contains an increasing
3-term arithmetic progression at increasing indices. -/
theorem exists_increasingAP3 (x : ℕ ≃ ℕ) : HasIncreasingAP3 x := by
  unfold HasIncreasingAP3
  have key : ∀ n : ℕ, x (x.symm n) = n := fun n ↦ x.apply_symm_apply n
  have hne : ∀ d : ℕ, 1 ≤ d → x.symm (x 0 + d) ≠ 0 := by
    intro d hd h0
    have h1 : x (x.symm (x 0 + d)) = x 0 + d := key _
    rw [h0] at h1
    omega
  by_cases h : ∃ d : ℕ, 1 ≤ d ∧ x.symm (x 0 + d) < x.symm (x 0 + 2 * d)
  · obtain ⟨d, hd, hlt⟩ := h
    have hA : x (x.symm (x 0 + d)) = x 0 + d := key _
    have hB : x (x.symm (x 0 + 2 * d)) = x 0 + 2 * d := key _
    refine ⟨0, x.symm (x 0 + d), x.symm (x 0 + 2 * d), Nat.pos_of_ne_zero (hne d hd), hlt,
      ?_, ?_, ?_⟩ <;> omega
  · have hstrict : ∀ d : ℕ, 1 ≤ d → x.symm (x 0 + 2 * d) < x.symm (x 0 + d) := by
      intro d hd
      have hle : ¬ x.symm (x 0 + d) < x.symm (x 0 + 2 * d) := fun hc ↦ h ⟨d, hd, hc⟩
      have hne2 : x.symm (x 0 + 2 * d) ≠ x.symm (x 0 + d) := by
        intro he
        have := x.symm.injective he
        omega
      omega
    have hdec : ∀ j : ℕ, x.symm (x 0 + 2 ^ (j + 1)) < x.symm (x 0 + 2 ^ j) := by
      intro j
      have h2 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [h2]
      exact hstrict (2 ^ j) Nat.one_le_two_pow
    have hbound : ∀ j : ℕ, x.symm (x 0 + 2 ^ j) + j ≤ x.symm (x 0 + 2 ^ 0) := by
      intro j
      induction j with
      | zero => omega
      | succ n ih =>
        have := hdec n
        omega
    have hfin := hbound (x.symm (x 0 + 2 ^ 0) + 1)
    exfalso
    omega

/-- **Davis–Entringer–Graham–Simmons (1977).** Every permutation of `ℕ` contains a monotone
3-term arithmetic progression. -/
theorem exists_monotoneAP3 (x : ℕ ≃ ℕ) : HasMonotoneAP3 x :=
  (exists_increasingAP3 x).hasMonotoneAP3

end Erdos196
