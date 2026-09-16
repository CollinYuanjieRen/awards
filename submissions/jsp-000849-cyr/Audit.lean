import Erdos1019Planar

open scoped SimpleGraph

#print axioms erdos_1019_saturated_planar
#print axioms erdos_1019_saturated_planar_closed
#print axioms Erdos1019.erdos_1019_sharp
#print axioms SimpleGraph.IsPlanar.of_isStraightLineDrawing
#print axioms top_four_isStraightLineDrawing
#print axioms Bipyramid.bipyramidGraph_isStraightLineDrawing
#print axioms fourCliqueGraph_edgeSet_ncard
#print axioms bipyramidGraph_saturated_planar

/-- The exact statement of Erdős Problem #1019 with topological planarity. -/
example {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V)
    (hE : G.edgeSet.ncard = Fintype.card V * Fintype.card V / 4 + (Fintype.card V + 1) / 2) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      H.IsPlanar ∧ 3 < Fintype.card W ∧ H.edgeSet.ncard = 3 * Fintype.card W - 6 ∧ H ⊑ G :=
  erdos_1019_saturated_planar G hE

/-- The closed form: no graph on `n + 1` vertices with the threshold number of edges avoids every
saturated planar graph on more than three vertices. -/
example :
    ¬ ∃ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
      G.edgeSet.ncard = (n + 1) * (n + 1) / 4 + (n + 1 + 1) / 2 ∧
        ∀ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
          H.IsPlanar → 3 < Fintype.card W → H.edgeSet.ncard = 3 * Fintype.card W - 6 → ¬ H ⊑ G :=
  erdos_1019_saturated_planar_closed
