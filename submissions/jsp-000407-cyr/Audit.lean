import Erdos508MoserSpindle

#print axioms hadwiger_nelson_at_least_four
#print axioms moser_dist_eq_one
#print axioms moser_no_three_colouring

/-- Erdős #508 (Hadwiger–Nelson), the classical lower bound, in the formal-conjectures shape
`4 ≤ χ(ℝ²)` with `χ(ℝ²) := SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ)`. -/
example : 4 ≤ SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ) :=
  hadwiger_nelson_at_least_four

/-- The graph is the unit-distance graph: adjacency is distance exactly one. -/
example (V : Set (EuclideanSpace ℝ (Fin 2))) (x y : V) :
    (UnitDistancePlaneGraph V).Adj x y ↔ dist x y = 1 := Iff.rfl
