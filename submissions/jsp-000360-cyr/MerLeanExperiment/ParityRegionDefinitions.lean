import MerLeanExperiment.DensityDefinitions

namespace Erdos441

noncomputable def parityRegion (A : Finset ℕ) (a b R : ℝ) (r : ℤ) : Finset ℕ := by
  classical
  exact A.filter fun n : ℕ => a * R < (n : ℝ) ∧ (n : ℝ) ≤ b * R ∧
    Even ((n : ℤ) - r)

noncomputable def consecutiveCell (A : Finset ℕ) (a delta R : ℝ) (r : ℤ)
    (s : ℕ) : Finset ℕ :=
  parityRegion A (a + s * delta) (a + (s + 1) * delta) R r

end Erdos441
