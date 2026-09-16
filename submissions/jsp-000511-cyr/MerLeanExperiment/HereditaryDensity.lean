import MerLeanExperiment.PlanarDensity
import MerLeanExperiment.PlaneBicoloring
import MerLeanExperiment.EdgeSupportedGraph
import MerLeanExperiment.DrawingAdapter

open scoped Graph
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}
noncomputable local instance decidableEqForHereditaryDensity : DecidableEq V := Classical.decEq V

/-- Every finite edge family satisfies the endpoint-density bound. -/
theorem PlaneDrawing.hereditary_density [Finite V]
    (D : PlaneDrawing G) (hbipartite : G.IsBipartite) (F : Finset G.edgeSet) :
    F.card ≤ 2 * (F.biUnion fun e => e.1.toFinset).card := by
  have hplaneFinite : D.planeGraph.Finite := D.planeGraph_finite
  have hplaneSimple : D.planeGraph.Simple := D.planeGraph_simple
  obtain ⟨c, hcolor⟩ := D.exists_bicoloring hbipartite
  obtain ⟨H, hHG, hedge, hvert⟩ := D.exists_edgeSupported_subgraph F
  have hHFinite : H.Finite := Graph.Finite.of_le hHG
  have hHSimple : H.Simple := Graph.Simple.anti hHG
  have hcolorH : ∀ (e : Sym2 V) (x y : Plane), H.IsLink e x y → c x ≠ c y :=
    fun e x y hxy => hcolor e x y (hxy.mono hHG)
  have hdensity := (D.isDrawing.mono hHG).bipartite_density c hcolorH
  omega

end PlanarListColoring
