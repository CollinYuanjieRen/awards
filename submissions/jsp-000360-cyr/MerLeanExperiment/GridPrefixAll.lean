import MerLeanExperiment.GridPrefixSmall
import MerLeanExperiment.GridPrefixCase3
import MerLeanExperiment.GridPrefixCase4

namespace Erdos441

theorem grid_prefix_all : ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L ≥ L0, ∀ T : ℤ,
    (L : ℤ) - 1 ≤ T → ∀ t : ℤ, -T ≤ t → t ≤ T →
    gridBetaPrefix (gridQ L) L T t ≤ gridCapacityPrefix (gridQ L) L T t := by
  obtain ⟨L3, hL3, h3⟩ := grid_prefix_case3
  obtain ⟨L4, hL4, h4⟩ := grid_prefix_case4
  refine ⟨max L3 L4, hL3.trans (le_max_left _ _), ?_⟩
  intro L hL T hT t htlo hthi
  have hLone : 1 ≤ L := hL3.trans ((le_max_left _ _).trans hL)
  have hT0 : 0 ≤ T := by omega
  obtain ⟨hq, _, _, _⟩ := grid_ratio_spec L hLone
  by_cases ht0 : t < 0
  · exact grid_prefix_case_neg (gridQ L) hq L hLone T t hT0 htlo ht0
  by_cases htL : t < (L : ℤ)
  · exact grid_prefix_case_small (gridQ L) hq L hLone T t hT0 hT (by omega) htL
  by_cases ht2L : t < 2 * (L : ℤ)
  · exact h3 L ((le_max_left _ _).trans hL) T t hT0 hthi (by omega) ht2L
  · exact h4 L ((le_max_right _ _).trans hL) T t hT0 hthi (by omega)

end Erdos441

#print axioms Erdos441.grid_prefix_all
