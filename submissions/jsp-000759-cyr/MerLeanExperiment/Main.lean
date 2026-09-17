import MerLeanExperiment.VertexRailsLeFour
import MerLeanExperiment.MaderDisproof
import MerLeanExperiment.MaderTheorem
import MerLeanExperiment.MaderCorollary

/-!
# Erdős Problem #915 (JSP-000759): the complete answer

The five faces frozen in `Target.lean` are proved in the imported modules under the same names:
`vertex_rails_of_le_four`, `exists_no_vertex_rails_of_ge_five`, `mader_edge_rails`,
`edge_rails_of_bollobas_erdos`, `edgeRailNumber_eq`.  This file bundles them.
-/

namespace Erdos915

/-- **Erdős #915, complete answer.**  For the Bollobás–Erdős question "a graph with `1 + n(m-1)`
vertices and `1 + n·C(m,2)` edges contains two vertices joined by `m` disjoint paths":
(i) true for `m = 2, 3, 4` under the internally-vertex-disjoint reading;
(ii) false for every `m ≥ 5` under that reading;
(iii) true for every `m ≥ 2` under the edge-disjoint reading;
(iv) in general `ℓ_m(n) = ⌊m(n-1)/2⌋ + 1` for `2 ≤ m ≤ n`. -/
theorem erdos_915 :
    (∀ {m n : ℕ}, 2 ≤ m → m ≤ 4 → 1 ≤ n → ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
        Fintype.card V = 1 + n * (m - 1) → G.edgeSet.ncard = 1 + n * m.choose 2 →
          HasVertexRails G m) ∧
    (∀ {m : ℕ}, 5 ≤ m → ∃ (n : ℕ) (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        1 ≤ n ∧ Fintype.card V = 1 + n * (m - 1) ∧ G.edgeSet.ncard = 1 + n * m.choose 2 ∧
          ¬ HasVertexRails G m) ∧
    (∀ {m n : ℕ}, 2 ≤ m → 1 ≤ n → ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
        Fintype.card V = 1 + n * (m - 1) → G.edgeSet.ncard = 1 + n * m.choose 2 →
          HasEdgeRails G m) ∧
    (∀ m n : ℕ, 2 ≤ m → m ≤ n →
        IsLeast {k : ℕ | ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          Fintype.card V = n → k ≤ G.edgeSet.ncard → HasEdgeRails G m} (m * (n - 1) / 2 + 1)) :=
  by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n hm2 hm4 hn V _ G hV hE
    exact vertex_rails_of_le_four hm2 hm4 hn G hV hE
  · intro m hm
    exact exists_no_vertex_rails_of_ge_five hm
  · intro m n hm2 hn V _ G hV hE
    exact edge_rails_of_bollobas_erdos hm2 hn G hV hE
  · intro m n hm hmn
    exact edgeRailNumber_eq m n hm hmn

end Erdos915
