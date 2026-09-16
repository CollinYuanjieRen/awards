import MerLeanExperiment.Kesten

/-! Public fixed-statement and foundational-axiom audit. -/

#print axioms Kesten.bounded_remainder_iff

example (α u v : ℝ) (hα : Irrational α) (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    Kesten.HasBoundedRemainder α u v ↔
      ∃ k l : ℤ, v - u = (k : ℝ) * α + (l : ℝ) := by
  exact Kesten.bounded_remainder_iff α u v hα hu huv hv

example (α u v : ℝ) (hα : Irrational α) (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(((Finset.range n).filter fun j ↦
          u ≤ Int.fract (α * (j + 1 : ℕ)) ∧
            Int.fract (α * (j + 1 : ℕ)) < v).card : ℝ) -
        (n : ℝ) * (v - u)| ≤ C) ↔
      ∃ k l : ℤ, v - u = (k : ℝ) * α + (l : ℝ) := by
  simpa only [Kesten.HasBoundedRemainder, Kesten.countInIco] using
    Kesten.bounded_remainder_iff α u v hα hu huv hv
