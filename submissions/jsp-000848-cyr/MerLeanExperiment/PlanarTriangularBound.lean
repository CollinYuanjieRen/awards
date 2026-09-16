import MerLeanExperiment.EulerFaceSystem
import MerLeanExperiment.SimpleCycleLength
import MerLeanExperiment.Vendor.Schoenflies.Graph.Redrawing

open scoped Graph
open Set Schoenflies

namespace Graph

/-- Every boundary in a simple face system has at least three edges. -/
theorem FaceSystem.three_mul_faceCount_le_boundaryLength
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Simple]
    (M : FaceSystem G drawing) : 3 * M.faceCount ≤ M.boundaryLength := by
  have hlength : ∀ q ∈ M.boundaries, 3 ≤ q.2.length := by
    intro q hq
    obtain ⟨z, e, a, b, D, hz, hU, hcycle, hperm⟩ := M.valid q hq
    rw [hperm.length_eq]
    exact hcycle.isCycle.three_le_length
  rw [FaceSystem.faceCount, FaceSystem.boundaryLength]
  calc
    3 * M.boundaries.card = ∑ q ∈ M.boundaries, 3 := by simp [Nat.mul_comm]
    _ ≤ ∑ q ∈ M.boundaries, q.2.length := by
      exact Finset.sum_le_sum fun q hq ↦ hlength q hq

/-- A finite two-connected simple plane graph satisfies the triangular planar edge bound. -/
theorem IsDrawing.twoConnected_triangular_density
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] [G.Simple] (h : IsDrawing G drawing) (htwo : G.IsTwoConnected) :
    E(G).ncard + 6 ≤ 3 * V(G).ncard := by
  obtain ⟨redrawing, hdraw, hpoly⟩ := polygonal_redrawing G drawing h
  obtain ⟨M, heuler, hboundary⟩ := hdraw.exists_euler_faceSystem hpoly htwo
  have hthree := M.three_mul_faceCount_le_boundaryLength
  omega

end Graph
