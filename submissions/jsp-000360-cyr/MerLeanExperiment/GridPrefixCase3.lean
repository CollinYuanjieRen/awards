import MerLeanExperiment.GridCapacity3
import MerLeanExperiment.GridScalar3

namespace Erdos441

theorem grid_prefix_case3 : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T t : ℤ,
    0 ≤ T → t ≤ T → (L : ℤ) ≤ t → t < 2 * (L : ℤ) →
    gridBetaPrefix (gridQ L) L T t ≤ gridCapacityPrefix (gridQ L) L T t := by
  obtain ⟨L0, hL0, hscalar⟩ := grid_case3_scalar
  refine ⟨L0, hL0, ?_⟩
  intro L hL T t hT htT hLt ht2L
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, hqL, hq2L, _⟩ := grid_ratio_spec L hLone
  have hqne : gridQ L ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hlu : Real.sqrt 2 ≤ gridQ L ^ t := by
    rw [← hqL]
    exact zpow_le_zpow_right₀ hq.le hLt
  have huu : gridQ L ^ t ≤ 2 / gridQ L := by
    calc
      _ ≤ gridQ L ^ (2 * (L : ℤ) - 1) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      _ = 2 / gridQ L := by rw [zpow_sub_one₀ hqne, hq2L, div_eq_mul_inv]
  have hnonneg := hscalar L hL (gridQ L ^ t) hlu huu
  exact (le_add_of_nonneg_right hnonneg).trans
    (grid_case3_capacity (gridQ L) hq L hLone hqL hq2L T t hT htT hLt ht2L)

end Erdos441

#print axioms Erdos441.grid_prefix_case3
