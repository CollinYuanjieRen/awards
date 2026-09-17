import Erdos661Lenz

#print axioms erdos_661_lenz
#print axioms Erdos661.dist_xPt_yPt

/-- Erdős #661, Lenz: for every `n`, `2n` distinct points in `ℝ^4` with all cross distances `1`. -/
example (n : ℕ) :
    ∃ x y : Fin n → EuclideanSpace ℝ (Fin 4), Function.Injective x ∧ Function.Injective y ∧
      (∀ i j, x i ≠ y j) ∧ ∀ i j, dist (x i) (y j) = 1 :=
  erdos_661_lenz n
