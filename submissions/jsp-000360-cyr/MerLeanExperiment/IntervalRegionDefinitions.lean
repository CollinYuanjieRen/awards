import MerLeanExperiment.DensityDefinitions

namespace Erdos441

noncomputable def intervalRegion (A : Finset ℕ) (a b R : ℝ) : Finset ℕ := by
  classical
  exact A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R

end Erdos441
