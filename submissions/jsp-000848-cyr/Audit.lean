import MerLeanExperiment

#check Erdos1018Topological.planeDrawing_top_of_cliqueSubdivision
#print axioms Erdos1018Topological.planeDrawing_top_of_cliqueSubdivision
#check Erdos1018Topological.no_drawing_of_cliqueSubdivision_five
#print axioms Erdos1018Topological.no_drawing_of_cliqueSubdivision_five
#check Erdos1018Topological.erdos_1018_ordinary_nonplanarity
#print axioms Erdos1018Topological.erdos_1018_ordinary_nonplanarity

example
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) ^ ((1 : ℝ) + ε) ≤ (G.edgeSet.ncard : ℝ) →
          ∃ S : G.Subgraph,
            S.verts.ncard ≤ C ∧ ¬ Nonempty (PlanarListColoring.PlaneDrawing S.coe) :=
  Erdos1018Topological.erdos_1018_ordinary_nonplanarity ε hε
