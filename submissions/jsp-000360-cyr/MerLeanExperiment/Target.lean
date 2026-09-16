import MerLeanExperiment.Asymptotic

namespace Erdos441

/-- The complete two-part statement of Erdős problem 441. -/
theorem erdos_441_complete :
    Filter.Tendsto (fun N : ℕ => (g N : ℝ) / Real.sqrt ((9 / 8 : ℝ) * N))
      Filter.atTop (nhds 1) ∧
    ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ (erdosConstruction N).card < g N := by
  exact ⟨chen_asymptotic, erdosConstruction_not_eventually_extremal⟩

end Erdos441
