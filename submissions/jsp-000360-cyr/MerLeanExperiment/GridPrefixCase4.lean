import MerLeanExperiment.GridCapacity4
import MerLeanExperiment.GridScalar4

namespace Erdos441

theorem grid_prefix_case4 : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T t : ℤ,
    0 ≤ T → t ≤ T → 2 * (L : ℤ) ≤ t →
    gridBetaPrefix (gridQ L) L T t ≤ gridCapacityPrefix (gridQ L) L T t := by
  obtain ⟨L0, hL0, hscalar⟩ := grid_case4_scalar
  refine ⟨L0, hL0, ?_⟩
  intro L hL T t hT htT ht2L
  have hLone : 1 ≤ L := hL0.trans hL
  obtain ⟨hq, hqL, hq2L, _⟩ := grid_ratio_spec L hLone
  have hu : 2 ≤ gridQ L ^ t := by
    rw [← hq2L]
    exact zpow_le_zpow_right₀ hq.le ht2L
  exact (le_add_of_nonneg_right (hscalar L hL (gridQ L ^ t) hu)).trans
    (grid_case4_capacity (gridQ L) hq L hLone hqL hq2L T t hT htT ht2L)

end Erdos441

#print axioms Erdos441.grid_prefix_case4
