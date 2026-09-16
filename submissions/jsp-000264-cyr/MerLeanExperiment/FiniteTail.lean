import Mathlib

namespace ReciprocalSquares

/-- An explicit finite reciprocal-square tail dominates a removed term with
uniform slack. This supplies the greedy argument without an infinite series. -/
theorem finite_reciprocal_square_tail (d : ℕ) (hd : 2 ≤ d) :
    (121 : ℚ) / (100 * (d : ℚ) ^ 2) <
      ∑ j ∈ Finset.Icc (d + 1) (20 * d), (1 : ℚ) / (j : ℚ) ^ 2 := by
  have htel : ∀ b : ℕ, d + 1 ≤ b →
      (∑ j ∈ Finset.Icc (d + 1) b,
        (1 : ℚ) / ((j : ℚ) * ((j : ℚ) + 1))) =
        1 / ((d : ℚ) + 1) - 1 / ((b : ℚ) + 1) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
      push_cast
      field_simp
      ring
    | succ b hb ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hb)]
      rw [ih]
      push_cast
      field_simp
      ring
  have htop : d + 1 ≤ 20 * d := by omega
  have hsum_le :
      (∑ j ∈ Finset.Icc (d + 1) (20 * d),
        (1 : ℚ) / ((j : ℚ) * ((j : ℚ) + 1))) ≤
        ∑ j ∈ Finset.Icc (d + 1) (20 * d), (1 : ℚ) / (j : ℚ) ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    have hjlow : d + 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjpos : 0 < (j : ℚ) := by
      exact_mod_cast (show 0 < j by omega)
    apply one_div_le_one_div_of_le (pow_pos hjpos 2)
    nlinarith
  have hdq : (2 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hshift : 0 ≤ (d : ℚ) - 2 := sub_nonneg.mpr hdq
  have hpoly :
      0 < 1900 * ((d : ℚ) - 2) ^ 3 + 8980 * ((d : ℚ) - 2) ^ 2 +
        10579 * ((d : ℚ) - 2) + 317 := by
    positivity
  have hrhs :
      1 / ((d : ℚ) + 1) - 1 / (20 * (d : ℚ) + 1) =
        19 * (d : ℚ) / (((d : ℚ) + 1) * (20 * (d : ℚ) + 1)) := by
    field_simp
    ring
  have hlower :
      (121 : ℚ) / (100 * (d : ℚ) ^ 2) <
        1 / ((d : ℚ) + 1) - 1 / (20 * (d : ℚ) + 1) := by
    rw [hrhs]
    rw [div_lt_div_iff₀]
    · nlinarith
    · positivity
    · positivity
  have htel_top :
      (∑ j ∈ Finset.Icc (d + 1) (20 * d),
        (1 : ℚ) / ((j : ℚ) * ((j : ℚ) + 1))) =
        1 / ((d : ℚ) + 1) - 1 / (20 * (d : ℚ) + 1) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using htel (20 * d) htop
  rw [← htel_top] at hlower
  exact hlower.trans_le hsum_le

end ReciprocalSquares
