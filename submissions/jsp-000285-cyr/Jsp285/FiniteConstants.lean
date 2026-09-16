import Mathlib

/-! Absolute constants and uniform elementary bounds for the multiset construction. -/

namespace Jsp285

/-- Partition depth amplification in the proved finite sum-tree theorem. -/
def partitionMass : ℕ := 200 ^ 49

/-- The finite occurrence theorem uses this absolute linear coefficient. -/
def finiteCoefficient : ℕ := 200000 * partitionMass

/-- A cubic in the binary logarithm is bounded uniformly, including small inputs. -/
lemma cube_succ_le_eight_pow (k : ℕ) : (k + 1) ^ 3 ≤ 8 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · have hk3 : 3 ≤ k := by omega
        have hsq : 9 ≤ k ^ 2 := by nlinarith
        have hcube := Nat.mul_le_mul_left k hsq
        calc
          (k + 1 + 1) ^ 3 ≤ 2 * (k + 1) ^ 3 := by nlinarith
          _ ≤ 2 * (8 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
          _ = 8 * 2 ^ (k + 1) := by ring

/-- The logarithmic extraction and pruning charges fit inside a linear budget. -/
lemma log_cube_le (n : ℕ) (hn : 0 < n) : (Nat.log 2 n + 1) ^ 3 ≤ 8 * n := by
  exact (cube_succ_le_eight_pow _).trans
    (Nat.mul_le_mul_left 8 (Nat.pow_log_le_self 2 hn.ne'))

/-- Total extraction and dyadic-pruning loss is linear in the original bound. -/
lemma extraction_prune_loss_bound (n H : ℕ) (hn : 0 < n) :
    ((Nat.log 2 n + 2) * (10000 * H * (Nat.log 2 n + 1))) * Nat.log 2 n +
      H * n + (Nat.log 2 n + 1) * (10000 * H * (Nat.log 2 n + 1)) ≤
        160001 * H * n := by
  have h := Nat.mul_le_mul_left (20000 * H) (log_cube_le n hn)
  nlinarith [Nat.zero_le (H * Nat.log 2 n)]

/-- Tracking at most three times the ambient bound fits the chosen threshold. -/
lemma tracking_threshold_le (n m H : ℕ) (hn : 0 < n) (hm : m ≤ 3 * n) :
    1000 * (Nat.log 2 (2 * m + 1) + 1) * H ≤
      10000 * H * (Nat.log 2 n + 1) := by
  have hbound : 2 * m + 1 ≤ 8 * n := by omega
  have hlog : Nat.log 2 (8 * n) = Nat.log 2 n + 3 := by
    rw [show 8 * n = ((n * 2) * 2) * 2 by ring]
    rw [Nat.log_mul_base (by omega) (by positivity),
      Nat.log_mul_base (by omega) (by positivity),
      Nat.log_mul_base (by omega) hn.ne']
  have hmono := Nat.log_mono_right (b := 2) hbound
  rw [hlog] at hmono
  have hscaled := Nat.mul_le_mul_right (1000 * H) hmono
  nlinarith [Nat.zero_le (H * Nat.log 2 n)]

end Jsp285
