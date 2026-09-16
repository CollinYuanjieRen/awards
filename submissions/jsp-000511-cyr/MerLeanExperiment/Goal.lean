import MerLeanExperiment.HereditaryDensity
import MerLeanExperiment.ColoringFromDensity
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace PlanarListColoring

/- Every finite bipartite graph with an ordinary crossing-free plane drawing
is colorable from arbitrary lists of three natural-number colors. -/
theorem planar_bipartite_three_list_colorable
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hplanar : Nonempty (PlaneDrawing G)) (hbipartite : G.IsBipartite)
    (L : V → Finset ℕ) (hL : ∀ v, (L v).card = 3) :
    ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v := by
  obtain ⟨D⟩ := hplanar
  exact three_list_colorable_of_density G
    (D.hereditary_density hbipartite) hbipartite L hL

end PlanarListColoring
