import Erdos704CubeColouring

#print axioms erdos_704_trivial_colouring
#print axioms erdos_704_chromaticNumber_le

/-- Erdős #704: the trivial cube-tiling colouring bound. -/
example (n : ℕ) : ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧ (k : ℝ) ≤ (2 + Real.sqrt n) ^ n :=
  erdos_704_trivial_colouring n
example (n : ℕ) : (unitDistanceGraph n).chromaticNumber ≤ (⌊(2 + Real.sqrt n) ^ n⌋₊ : ℕ∞) :=
  erdos_704_chromaticNumber_le n

/-- The unit-distance graph, unfolded. -/
example (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) : (unitDistanceGraph n).Adj x y ↔ dist x y = 1 := Iff.rfl
