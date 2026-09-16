import MerLeanExperiment.CycleFaceSystem
import MerLeanExperiment.CycleCounts
import MerLeanExperiment.EarFaceSystem
import MerLeanExperiment.EarCounts
import Mathlib.Combinatorics.Graph.Simple

open scoped Graph
open Set Schoenflies

namespace Graph

/-- Euler's formula and twice-per-edge boundary counting are constructed from an ordinary
polygonal drawing by cycle-and-ear induction. They are conclusions, not drawing certificates. -/
theorem IsDrawing.exists_euler_faceSystem
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Loopless] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (htwo : G.IsTwoConnected) :
    ∃ M : FaceSystem G drawing,
      V(G).ncard + M.faceCount = E(G).ncard + 2 ∧
      M.boundaryLength = 2 * E(G).ncard := by
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x ↦ Graph.not_isLoopAt G g x
  obtain ⟨e, u, v, D, w, hlong⟩ := htwo.exists_long_cycle hnl
  let motive := fun B : Graph Plane β ↦
    ∃ M : FaceSystem B drawing,
      V(B).ncard + M.faceCount = E(B).ncard + 2 ∧
      M.boundaryLength = 2 * E(B).ncard
  apply htwo.ear_decomposition (motive := motive) hnl hlong.isTwoConnected
    hlong.isCycle.cycleGraph_le
  · obtain ⟨M, hfaces, hlength⟩ :=
      h.exists_cycle_faceSystem hpoly hlong.isCycle
    refine ⟨M, ?_, ?_⟩
    · rw [hlong.isCycle.ncard_cycleGraph_vertices,
        hlong.isCycle.ncard_cycleGraph_edges, hfaces]
    · rw [hlength, hlong.isCycle.ncard_cycleGraph_edges]
  · intro B a b P _htwoB _hcycleB hBG hmot hpath hab ha hb hint
    rcases ear_edges_notMem_or_union_eq hBG hpath hab ha hb hint with hnew | heq
    · obtain ⟨M, heuler, hsum⟩ := hmot
      obtain ⟨M', hfaces, hlength⟩ :=
        h.exists_ear_faceSystem hpoly hBG M hpath hab ha hb hint hnew
      refine ⟨M', ?_, ?_⟩
      · have hvert := ncard_vertices_union_ear hBG hpath hab ha hb hint
        have hedge := ncard_edges_union_ear hBG hpath hnew
        omega
      · have hedge := ncard_edges_union_ear hBG hpath hnew
        omega
    · rw [heq]
      exact hmot

end Graph
