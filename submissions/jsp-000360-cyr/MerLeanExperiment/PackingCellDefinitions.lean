import MerLeanExperiment.TranslationDefinitions
import MerLeanExperiment.CellDefinitions

namespace Erdos441

noncomputable def packingCell {K : ℕ} (A : Finset ℕ) (r : Fin K → ℤ)
    (c : Fin K → ℝ) (delta R : ℝ) (i : Fin K) : Finset ℕ := by
  classical
  exact A.filter fun n => c i * R < (n : ℝ) ∧ (n : ℝ) ≤ (c i + delta) * R ∧
    Even ((n : ℤ) - r i)

noncomputable def packingCellUnion {K : ℕ} (A : Finset ℕ) (r : Fin K → ℤ)
    (c : Fin K → ℝ) (delta R : ℝ) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion (packingCell A r c delta R)

noncomputable def packingBadPoints (A : Finset ℕ) (D : ℕ) (B R : ℝ) : Finset ℕ := by
  classical
  exact A.filter fun n => (n : ℝ) ≤ B * R ∧ ¬ Nat.Coprime n D

end Erdos441
