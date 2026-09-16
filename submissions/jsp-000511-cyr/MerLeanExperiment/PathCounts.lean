import MerLeanExperiment.Vendor.Schoenflies.Graph.PathGraph
import Mathlib.Data.Set.Card

open scoped Graph
open Set

namespace Graph

variable {α β : Type*} {G : Graph α β} {a b c : α} {e : β} {W : List β}

/-- The visited vertices of a first step are its source plus the remaining visited vertices. -/
theorem walkVertices_cons_eq (he : G.IsLink e a b) :
    G.walkVertices a (e :: W) = insert a (G.walkVertices b W) := by
  exact walkVertices_cons he

/-- A simple path visits one more vertex than its number of edges. -/
theorem IsPath.ncard_walkVertices (h : G.IsPath a W b) :
    (G.walkVertices a W).ncard = W.length + 1 := by
  induction h with
  | nil => simp [walkVertices_nil]
  | cons he hW hfresh ih =>
      rw [walkVertices_cons he, Set.ncard_insert_of_notMem hfresh hW.isWalk.finite_walkVertices,
        ih]
      simp

/-- The edge set of the graph spanned by a simple path has exactly the path length. -/
theorem IsPath.ncard_pathGraphOf_edges (h : G.IsPath a W b) :
    E(G.pathGraphOf a W).ncard = W.length := by
  classical
  rw [pathGraphOf_edgeSet h.isWalk]
  have hset : {e | e ∈ W} = (↑W.toFinset : Set β) := by
    ext f
    simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup h.nodup]

end Graph
