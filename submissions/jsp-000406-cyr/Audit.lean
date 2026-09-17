import Erdos507Heilbronn

open Asymptotics Filter Topology

#print axioms erdos_507_trivial_bounds
#print axioms erdos_507_upper_trivial
#print axioms erdos_507_lower_erdos

/-- Erdős #507 (Heilbronn), the elementary bounds, in the formal-conjectures shapes
`erdos_507.variants.upper_trivial` and `lower_erdos` (`≪`/`≫` unfolded to `IsBigO atTop`). -/
example : α =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := erdos_507_upper_trivial
example : (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) =O[atTop] α := erdos_507_lower_erdos

/-- The definitions are the formal-conjectures ones. -/
example (n : ℕ) : α n = sSup (minTriangleArea '' { S : Finset (EuclideanSpace ℝ (Fin 2)) |
    S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ¬ Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2))) }) := rfl
