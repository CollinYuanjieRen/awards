import MerLeanExperiment.GridNegativeFour
import MerLeanExperiment.GridPositiveFour
import MerLeanExperiment.GridPrefixIdentity
import MerLeanExperiment.GridScalarDefinitions
import MerLeanExperiment.FloorBranches

namespace Erdos441

theorem grid_case4_capacity (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (hqL : q ^ (L : ℤ) = Real.sqrt 2) (hq2L : q ^ (2 * (L : ℤ)) = 2)
    (T t : ℤ) (hT : 0 ≤ T) (htT : t ≤ T) (ht2L : 2 * (L : ℤ) ≤ t) :
    gridBetaPrefix q L T t +
      (q ^ t * gridSlope4 q + 2 - 3 * Real.sqrt 2 / 2 + gridEta * Real.sqrt 2 -
        q / (4 * q ^ t)) ≤ gridCapacityPrefix q L T t := by
  have hqpos : 0 < q := by linarith
  have ht0 : 0 ≤ t := by omega
  have hu : 2 ≤ q ^ t := by
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le ht2L
  have hup : 0 < q ^ t := zpow_pos hqpos _
  let n : ℝ := ⌊q ^ t⌋₊
  have hnhi : n ≤ q ^ t := Nat.floor_le hup.le
  have hnlo : q ^ t - 1 ≤ n := by
    have hh := Nat.lt_floor_add_one (q ^ t)
    dsimp [n]
    linarith
  have hscalar : (2 - q) * q ^ t - q / (4 * q ^ t) ≤
      2 * n - q * n ^ 2 / q ^ t + gridExtra4 q T t := by
    by_cases hn : q ^ t - 1 / 2 ≤ n
    · have h := floor_branch_one q (q ^ t) n hq.le hu hn hnhi
      have he := grid_extra4_nonneg q hq T t
      linarith
    · have hn' : n < q ^ t - 1 / 2 := lt_of_not_ge hn
      have h := floor_branch_two q (q ^ t) n hq.le hu hnlo hn'.le
      have he := grid_extra4_lower q hq T t hT ht0 htT hu hn'
      have heq : 2 * n - q * n * (n + 1) / q ^ t + q ^ t / (n + 1) =
          2 * n - q * n ^ 2 / q ^ t + (q ^ t / (n + 1) - q * n / q ^ t) := by ring
      rw [heq] at h
      change q ^ t / (n + 1) - q * n / q ^ t ≤ gridExtra4 q T t at he
      linarith
  have hneg := grid_case4_negative_columns q hq T t hT ht0 htT hu
  have hpos := grid_case4_positive_columns q hq L hL hqL hq2L t ht2L
  have hcap := grid_capacity_prefix_eq q hq L hL T t hT (by omega)
  simp only [ht0, ↓reduceIte] at hcap
  have hex : 0 ≤ 1 - q ^ (-1 : ℤ) := by
    have hh : q ^ (-1 : ℤ) ≤ q ^ (0 : ℤ) := zpow_le_zpow_right₀ hq.le (by norm_num)
    exact sub_nonneg.mpr (by simpa only [zpow_zero] using hh)
  have hbeta := grid_beta_prefix_eq q hqpos.ne' L T t hT (by omega)
  rw [hqL, zpow_add₀ hqpos.ne', zpow_one] at hbeta
  rw [hcap, hbeta]
  unfold gridSlope4
  change 2 * n - q * n ^ 2 / q ^ t - q ^ (-T) + gridExtra4 q T t ≤ _ at hneg
  have halg : (q ^ t * q - q ^ (-T) + gridEta * (q ^ t * q - Real.sqrt 2)) +
      (q ^ t * (2 - 2 * q + (1 - q / 2) / (2 * (1 + q)) - gridEta * q) +
        2 - 3 * Real.sqrt 2 / 2 + gridEta * Real.sqrt 2 - q / (4 * q ^ t)) =
      ((2 - q) * q ^ t - q / (4 * q ^ t)) - q ^ (-T) +
        (q ^ t / (2 * (1 + q)) * (1 - q / 2) + 2 - 3 * Real.sqrt 2 / 2) := by ring
  rw [halg]
  linarith

end Erdos441

#print axioms Erdos441.grid_case4_capacity
