import MerLeanExperiment.PathCounts
import MerLeanExperiment.Vendor.Schoenflies.FaceCycles

open scoped Graph
open Set

namespace Graph

variable {α β : Type*} {G : Graph α β} {a b : α} {e : β} {W : List β}

/-- The cycle graph has one vertex per boundary edge. -/
theorem IsCycleThrough.ncard_cycleGraph_vertices (h : G.IsCycleThrough e a b W) :
    V(G.cycleGraph a e W).ncard = (e :: W).length := by
  rw [h.cycleGraph_vertexSet, h.isPath.ncard_walkVertices]
  simp

/-- The cycle graph's boundary edge list enumerates its edges without repetition. -/
theorem IsCycleThrough.ncard_cycleGraph_edges (h : G.IsCycleThrough e a b W) :
    E(G.cycleGraph a e W).ncard = (e :: W).length := by
  classical
  rw [h.cycleGraph_edgeSet]
  have hn_cons : (e :: W).Nodup := List.nodup_cons.2 ⟨h.notMem, h.isPath.nodup⟩
  have hn : (W ++ [e]).Nodup := List.nodup_append_comm.mp (by simpa using hn_cons)
  have hset : {f | f ∈ W ++ [e]} = (↑(W ++ [e]).toFinset : Set β) := by
    ext f
    simp [or_comm]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hn]
  simp

end Graph
