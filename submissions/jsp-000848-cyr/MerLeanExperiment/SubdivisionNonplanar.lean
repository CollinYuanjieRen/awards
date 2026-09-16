import MerLeanExperiment.SubdivisionDrawing
import MerLeanExperiment.CompleteFive

namespace Erdos1018Topological

open PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A graph containing a subdivision of `K₅` has no ordinary crossing-free plane drawing. -/
theorem no_drawing_of_cliqueSubdivision_five
    (s : Erdos1018.CliqueSubdivision G 5) :
    ¬ Nonempty (PlaneDrawing G) := by
  rintro ⟨D⟩
  exact completeFive_no_drawing (planeDrawing_top_of_cliqueSubdivision D s)

end Erdos1018Topological
