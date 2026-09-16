import MerLeanExperiment.PackingCellDefinitions

namespace Erdos441

noncomputable def parityDensity (A : Finset ℕ) (a b R : ℝ) (r : ℤ) : ℝ := by
  classical
  exact ((A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R ∧
    Even ((n : ℤ) - r)).card : ℝ) / ((b - a) * R)

noncomputable def intervalDensity (A : Finset ℕ) (a b R : ℝ) : ℝ := by
  classical
  exact ((A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R).card : ℝ) /
    ((b - a) * R)

end Erdos441
