import MerLeanExperiment.GridDefinitions

namespace Erdos441

/-- Actual reflected extra-point incidence sum in the fourth grid case. -/
noncomputable def gridExtra4 (q : ℝ) (T t : ℤ) : ℝ := by
  classical
  exact ∑ a ∈ Finset.Icc (⌊q ^ t⌋₊ + 1) ⌊q ^ t + 1 / 2⌋₊,
    ∑ j ∈ Finset.Icc (-T) (-1),
      if (a : ℝ) ≤ min (q ^ t * q ^ j + 1) (q ^ t / q ^ j)
      then q ^ j * (q - 1) else 0

end Erdos441
