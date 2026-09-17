import MerLeanExperiment.RailsThree
import MerLeanExperiment.RailsFour

/-!
# Erdős #915 for `2 ≤ m ≤ 4`: the affirmative range

The Bollobás–Erdős question asks whether a graph on `1 + n(m-1)` vertices with `1 + n·C(m,2)`
edges must contain two vertices joined by `m` disjoint paths.  Under the vertex-disjoint
reading the answer is yes exactly for `m = 2, 3, 4`; this file assembles the three individual
cases (trivial, Bártfai 1960, Bollobás 1966) into the single frozen face
`vertex_rails_of_le_four`, and derives the edge-disjoint companion from it.
-/

namespace Erdos915

open SimpleGraph

/-- The Bollobás–Erdős conjecture is true for `m = 2, 3, 4` (vertex-disjoint reading). -/
theorem vertex_rails_of_le_four {m n : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hn : 1 ≤ n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (m - 1)) (hE : G.edgeSet.ncard = 1 + n * m.choose 2) :
    HasVertexRails G m := by
  interval_cases m
  · exact vertex_rails_two hn G hV hE
  · exact vertex_rails_three hn G hV hE
  · exact vertex_rails_four hn G hV hE

/-- The Bollobás–Erdős conjecture is true for `m = 2, 3, 4` in the edge-disjoint reading too:
internally vertex-disjoint paths between two distinct vertices are edge-disjoint. -/
theorem edge_rails_of_le_four {m n : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hn : 1 ≤ n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (m - 1)) (hE : G.edgeSet.ncard = 1 + n * m.choose 2) :
    HasEdgeRails G m :=
  hasEdgeRails_of_hasVertexRails G m (vertex_rails_of_le_four hm2 hm4 hn G hV hE)

#print axioms vertex_rails_of_le_four
#print axioms edge_rails_of_le_four

end Erdos915
