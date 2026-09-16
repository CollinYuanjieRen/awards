import MerLeanExperiment.CollisionDefinitions
import Mathlib.Data.Int.Interval

namespace Erdos441

noncomputable def goodTranslateUnion {K : ℕ} (A : Finset ℕ) (D : ℕ)
    (y : Fin K → ℤ) (H : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 H).biUnion fun h =>
    (Finset.univ.filter fun i => (y i + 2 * h).natAbs ∈ A ∧
      Nat.Coprime (y i + 2 * h).natAbs D).image fun i => (y i + 2 * h).natAbs

end Erdos441
