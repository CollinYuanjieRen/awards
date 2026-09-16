import Proof

open Erdos803

#print axioms Erdos803.alon_construction
#print axioms Erdos803.not_erdosSimonovitsUniform
#print axioms Erdos803.not_erdosSimonovitsLiteral

example : ∀ D : ℝ, 1 ≤ D → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ G : SimpleGraph (Fin N),
    (N : ℝ) * Real.logb 2 N ≤ G.edgeSet.ncard ∧
      ∀ H : G.Subgraph, Balanced D H →
        (H.edgeSet.ncard : ℝ) ≤ 18 * H.verts.ncard *
          (4 * Real.sqrt (Real.logb 2 H.verts.ncard) + Real.logb 2 (64 * D) + 26) :=
  Erdos803.alon_construction

example : ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsUniform ε D :=
  Erdos803.not_erdosSimonovitsUniform

example : ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsLiteral ε D :=
  Erdos803.not_erdosSimonovitsLiteral

#print Erdos803.sdeg
#print Erdos803.Balanced
#print Erdos803.ErdosSimonovitsUniform
#print Erdos803.ErdosSimonovitsLiteral
