import MerLeanExperiment.EulerFaceSystem
import MerLeanExperiment.SimpleCycleLength
import MerLeanExperiment.Vendor.Schoenflies.Graph.Redrawing

open scoped Graph
open Set Schoenflies

namespace Graph

/-- Every boundary in a bipartite simple face system has at least four edges. -/
theorem FaceSystem.four_mul_faceCount_le_boundaryLength
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Simple]
    (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y)
    (M : FaceSystem G drawing) : 4 * M.faceCount ≤ M.boundaryLength := by
  have hlength : ∀ q ∈ M.boundaries, 4 ≤ q.2.length := by
    intro q hq
    obtain ⟨z, e, a, b, D, hz, hU, hcycle, hperm⟩ := M.valid q hq
    rw [hperm.length_eq]
    exact hcycle.isCycle.four_le_length_of_bicoloring c hcolor
  rw [FaceSystem.faceCount, FaceSystem.boundaryLength]
  calc
    4 * M.boundaries.card = ∑ q ∈ M.boundaries, 4 := by simp [Nat.mul_comm]
    _ ≤ ∑ q ∈ M.boundaries, q.2.length := by
      exact Finset.sum_le_sum fun q hq => hlength q hq

/-- A finite two-connected bipartite plane graph satisfies the sharp planar edge bound. -/
theorem IsDrawing.twoConnected_density
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Simple] (h : IsDrawing G drawing) (htwo : G.IsTwoConnected)
    (c : Plane → Fin 2)
    (hcolor : ∀ (e : β) (x y : Plane), G.IsLink e x y → c x ≠ c y) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨redrawing, hdraw, hpoly⟩ := polygonal_redrawing G drawing h
  obtain ⟨M, heuler, hboundary⟩ := hdraw.exists_euler_faceSystem hpoly htwo
  have hfour := M.four_mul_faceCount_le_boundaryLength c hcolor
  omega

end Graph
