import MerLeanExperiment.SubdivisionNonplanar

namespace Erdos1018Topological

theorem erdos_1018_ordinary_nonplanarity
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) ^ ((1 : ℝ) + ε) ≤ (G.edgeSet.ncard : ℝ) →
          ∃ S : G.Subgraph,
            S.verts.ncard ≤ C ∧ ¬ Nonempty (PlanarListColoring.PlaneDrawing S.coe) := by
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by norm_num)
  obtain ⟨N, hgap⟩ := Erdos1018.exponent_gap ε hε
  let R : ℕ := Nat.ceil ((20 : ℝ) / δ)
  let C : ℕ := 5 + 10 * (2 * R + 1)
  refine ⟨C, max N 1, ?_⟩
  intro n hnLarge G hEdges
  have hN : N ≤ n := (le_max_left N 1).trans hnLarge
  have hnOne : 1 ≤ n := (le_max_right N 1).trans hnLarge
  have hn : 0 < n := Nat.zero_lt_of_lt hnOne
  have hDense : (4 : ℝ) ^ 25 * (n : ℝ) ^ ((1 : ℝ) + δ) ≤
      (G.edgeSet.ncard : ℝ) :=
    (hgap n hN).trans hEdges
  obtain ⟨s, hsbound⟩ :=
    Erdos1018.kostochka_pyber_compact_k5 δ hδ n hn G hDense
  let U : Set (Fin n) := Erdos1018.cliqueSubdivisionVerts s
  let T : G.Subgraph := Erdos1018.inducedSubgraph G U
  have hsT : Erdos1018.CliqueSubdivision T.coe 5 := by
    change Erdos1018.CliqueSubdivision (Erdos1018.inducedSubgraph G U).coe 5
    rw [Erdos1018.inducedSubgraph_coe]
    exact Erdos1018.restrictCliqueSubdivisionInduce s
      (fun i => s.branch_mem_verts i)
      (fun e x hx => s.support_mem_verts e hx)
  refine ⟨T, ?_, no_drawing_of_cliqueSubdivision_five hsT⟩
  change (Erdos1018.inducedSubgraph G U).verts.ncard ≤ C
  rw [Erdos1018.inducedSubgraph_verts]
  simpa [C, R] using hsbound

end Erdos1018Topological
