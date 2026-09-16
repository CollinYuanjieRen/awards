import MerLeanExperiment.GridDefinitions

namespace Erdos441

/-- The exact capacity-minus-beta residual in Chen's third grid case. -/
noncomputable def gridResidual3 (q u : ℝ) : ℝ :=
  9 * Real.sqrt 2 / 4 + Real.sqrt 2 * gridEta + 1 - 1 / q +
    u * (-q / 2 - 1 / 4 - gridEta * q) - 3 / u

/-- The coefficient and common endpoint remainder in Chen's fourth grid case. -/
noncomputable def gridSlope4 (q : ℝ) : ℝ :=
  2 - 2 * q + (1 - q / 2) / (2 * (1 + q)) - gridEta * q

noncomputable def gridResidual4 (q : ℝ) : ℝ :=
  2 * gridSlope4 q + 2 - 3 * Real.sqrt 2 / 2 + gridEta * Real.sqrt 2 - q / 8

end Erdos441
