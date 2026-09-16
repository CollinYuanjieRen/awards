import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Finite sums of bounded sequences change by a bounded amount under an integer shift. -/

namespace Kesten

/-- A sum of adjacent differences telescopes, with an arbitrary integer starting index. -/
private lemma sum_adjacent_sub (a : ℤ → ℝ) (z : ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (a (z + (j + 1 : ℕ)) - a (z + (j : ℕ))) =
      a (z + (n : ℕ)) - a z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The desired shift bound when the integer shift is a natural number. -/
private lemma shift_nat_bound (a : ℤ → ℝ) (ha : ∀ i : ℤ, |a i| ≤ 1) (m n : ℕ) :
    |∑ j ∈ Finset.range n, (a ((j : ℤ) + m) - a j)| ≤ 2 * (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsplit :
          (∑ j ∈ Finset.range n, (a ((j : ℤ) + (m + 1 : ℕ)) - a j)) =
            (∑ j ∈ Finset.range n,
              (a ((j : ℤ) + (m + 1 : ℕ)) - a ((j : ℤ) + m))) +
            ∑ j ∈ Finset.range n, (a ((j : ℤ) + m) - a j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hstep :
          (∑ j ∈ Finset.range n,
            (a ((j : ℤ) + (m + 1 : ℕ)) - a ((j : ℤ) + m))) =
            a ((n : ℤ) + m) - a m := by
        simpa [add_assoc, add_comm, add_left_comm] using sum_adjacent_sub a m n
      calc
        |∑ j ∈ Finset.range n, (a ((j : ℤ) + (m + 1 : ℕ)) - a j)| =
            |(a ((n : ℤ) + m) - a m) +
              ∑ j ∈ Finset.range n, (a ((j : ℤ) + m) - a j)| := by
                rw [hsplit, hstep]
        _ ≤ |a ((n : ℤ) + m) - a m| +
              |∑ j ∈ Finset.range n, (a ((j : ℤ) + m) - a j)| := abs_add_le _ _
        _ ≤ 2 + 2 * (m : ℝ) := by
          apply add_le_add
          · calc
              |a ((n : ℤ) + m) - a m| ≤ |a ((n : ℤ) + m)| + |a m| := abs_sub _ _
              _ ≤ 2 := by linarith [ha ((n : ℤ) + m), ha m]
          · exact ih
        _ = 2 * ((m + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The desired shift bound for the negative of a natural-number shift. -/
private lemma shift_neg_nat_bound (a : ℤ → ℝ) (ha : ∀ i : ℤ, |a i| ≤ 1) (m n : ℕ) :
    |∑ j ∈ Finset.range n, (a ((j : ℤ) - m) - a j)| ≤ 2 * (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsplit :
          (∑ j ∈ Finset.range n, (a ((j : ℤ) - (m + 1 : ℕ)) - a j)) =
            (∑ j ∈ Finset.range n,
              (a ((j : ℤ) - (m + 1 : ℕ)) - a ((j : ℤ) - m))) +
            ∑ j ∈ Finset.range n, (a ((j : ℤ) - m) - a j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hstep :
          (∑ j ∈ Finset.range n,
            (a ((j : ℤ) - (m + 1 : ℕ)) - a ((j : ℤ) - m))) =
            a (-(m : ℤ) - 1) - a ((n : ℤ) - m - 1) := by
        calc
          _ = -(∑ j ∈ Finset.range n,
                (a (-(m : ℤ) - 1 + (j + 1 : ℕ)) -
                  a (-(m : ℤ) - 1 + (j : ℕ)))) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              push_cast
              ring_nf
          _ = -(a (-(m : ℤ) - 1 + (n : ℕ)) - a (-(m : ℤ) - 1)) := by
              rw [sum_adjacent_sub]
          _ = a (-(m : ℤ) - 1) - a ((n : ℤ) - m - 1) := by
              ring_nf
      calc
        |∑ j ∈ Finset.range n, (a ((j : ℤ) - (m + 1 : ℕ)) - a j)| =
            |(a (-(m : ℤ) - 1) - a ((n : ℤ) - m - 1)) +
              ∑ j ∈ Finset.range n, (a ((j : ℤ) - m) - a j)| := by
                rw [hsplit, hstep]
        _ ≤ |a (-(m : ℤ) - 1) - a ((n : ℤ) - m - 1)| +
              |∑ j ∈ Finset.range n, (a ((j : ℤ) - m) - a j)| := abs_add_le _ _
        _ ≤ 2 + 2 * (m : ℝ) := by
          apply add_le_add
          · calc
              |a (-(m : ℤ) - 1) - a ((n : ℤ) - m - 1)| ≤
                  |a (-(m : ℤ) - 1)| + |a ((n : ℤ) - m - 1)| := abs_sub _ _
              _ ≤ 2 := by linarith [ha (-(m : ℤ) - 1), ha ((n : ℤ) - m - 1)]
          · exact ih
        _ = 2 * ((m + 1 : ℕ) : ℝ) := by push_cast; ring

/-- Shifting a uniformly unit-bounded integer sequence changes any initial finite sum by at
most twice the magnitude of the shift. -/
theorem shift_sum_bound (a : ℤ → ℝ) (ha : ∀ i : ℤ, |a i| ≤ 1) (k : ℤ) (n : ℕ) :
    |∑ j ∈ Finset.range n, (a ((j : ℤ) + k) - a j)| ≤ 2 * (k.natAbs : ℝ) := by
  cases k with
  | ofNat m => simpa using shift_nat_bound a ha m n
  | negSucc m =>
      rw [Int.natAbs_negSucc]
      convert shift_neg_nat_bound a ha (m + 1) n using 1
      simp [Int.negSucc_eq, sub_eq_add_neg]

end Kesten
