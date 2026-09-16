import MerLeanExperiment.GridPointCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos441

/-- Chen's geometric ratio; the proof uses only positive L. -/
noncomputable def gridQ (L : ℕ) : ℝ := (2 : ℝ) ^ (1 / (2 * (L : ℝ)))

noncomputable def gridEta : ℝ := (10 - 7 * Real.sqrt 2) / 32

/-- Actual nested integer sets, with integer exponents throughout. -/
noncomputable def gridA (q : ℝ) (i j : ℤ) : Finset ℤ :=
  if j ≤ i then gridPoints (q ^ j) (q ^ i) else ∅

/-- Column L is the exceptional singleton column from Chen, not a set difference. -/
noncomputable def gridCount (q : ℝ) (L : ℕ) (i j : ℤ) : ℕ :=
  if j = (L : ℤ) then (if i = 0 then 1 else 0)
  else if j < (L : ℤ) then (gridA q i j \ gridA q (i - 1) j).card else 0

noncomputable def gridBeta (q : ℝ) (L : ℕ) (i : ℤ) : ℝ :=
  if i < (L : ℤ) then q ^ i * (q - 1)
  else (1 + gridEta) * q ^ i * (q - 1)

noncomputable def gridDelta (q : ℝ) (L : ℕ) (j : ℤ) : ℝ :=
  if j < 0 then q ^ j * (q - 1)
  else if j < (L : ℤ) then (q - 1) / 2 * (q ^ j - q ^ (-j - 1))
  else if j = (L : ℤ) then 1 - q ^ (-1 : ℤ) else 0

noncomputable def gridBetaPrefix (q : ℝ) (L : ℕ) (T t : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc (-T) t, gridBeta q L i

noncomputable def gridCapacityPrefix (q : ℝ) (L : ℕ) (T t : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc (-T) t,
    ∑ j ∈ Finset.Icc (-T) (L : ℤ), gridDelta q L j * (gridCount q L i j : ℝ)

end Erdos441
