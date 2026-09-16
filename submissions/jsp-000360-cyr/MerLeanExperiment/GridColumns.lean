import MerLeanExperiment.GridDefinitions

namespace Erdos441

theorem grid_column_mono (q : ℝ) (hq : 1 < q) (i i' j : ℤ) (hii : i ≤ i') :
    gridA q i j ⊆ gridA q i' j := by
  intro z hz
  by_cases hji : j ≤ i
  · have hji' : j ≤ i' := hji.trans hii
    have hz' : z ∈ gridPoints (q ^ j) (q ^ i) := by simpa [gridA, hji] using hz
    simpa [gridA, hji'] using
      grid_points_mono (q ^ j) (q ^ i) (q ^ i') (zpow_pos (by linarith) _)
        (zpow_le_zpow_right₀ (le_of_lt hq) hii) hz'
  · simp [gridA, hji] at hz

theorem zero_mem_grid_column (q : ℝ) (hq : 1 < q) (i j : ℤ) (hji : j ≤ i) :
    (0 : ℤ) ∈ gridA q i j := by
  simp only [gridA, hji, ↓reduceIte, mem_gridPoints]
  right
  have hqpos : 0 < q := by linarith
  have hqjpos : 0 < q ^ j := zpow_pos hqpos _
  have hpowle : q ^ j ≤ q ^ i := zpow_le_zpow_right₀ (le_of_lt hq) hji
  have hratio : 1 ≤ q ^ i / q ^ j := (le_div_iff₀ hqjpos).mpr (by simpa using hpowle)
  have hprod : 0 ≤ q ^ j * q ^ i := mul_nonneg (zpow_nonneg hqpos.le _) (zpow_nonneg hqpos.le _)
  constructor
  · have : 0 ≤ min (q ^ j * q ^ i) (q ^ i / q ^ j - 1) :=
      le_min hprod (by linarith)
    linarith
  · norm_num

theorem zero_one_subset_grid_column (q : ℝ) (hq : 1 < q) (i j : ℤ)
    (hji : j ≤ i) (hsum : 0 ≤ i + j) :
    ({0, 1} : Finset ℤ) ⊆ gridA q i j := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact zero_mem_grid_column q hq i j hji
  · simp only [gridA, hji, ↓reduceIte, mem_gridPoints]
    left
    constructor
    · norm_num
    · have hqpos : 0 < q := by linarith
      have hone : 1 ≤ q ^ (j + i) := one_le_zpow₀ (le_of_lt hq) (by omega)
      rw [zpow_add₀ hqpos.ne'] at hone
      exact_mod_cast hone

end Erdos441
