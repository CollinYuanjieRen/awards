import Erdos265Cantor

#print axioms erdos_265_cantor

/-- Erdős #265: Cantor's sequence `C(n, 2)` (for `n ≥ 3`) has both reciprocal sums rational. -/
example : ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 2 ≤ a n) ∧
    (∃ q : ℚ, HasSum (fun n ↦ (1 : ℝ) / (a n : ℝ)) (q : ℝ)) ∧
    (∃ q : ℚ, HasSum (fun n ↦ (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ)) := erdos_265_cantor
