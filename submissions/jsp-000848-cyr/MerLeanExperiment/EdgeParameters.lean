import MerLeanExperiment.DrawingBasics
import MerLeanExperiment.GraphRepresentation

open scoped unitInterval
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Extend a drawn edge to real parameters by clamping to the closed unit interval. -/
noncomputable def PlaneDrawing.edgeParam (D : PlaneDrawing G) (e : G.edgeSet)
    (t : ℝ) : Plane :=
  WithLp.toLp 2 (D.edgePoint e (Set.projIcc 0 1 zero_le_one t))

/-- The extended real-parameter curve is continuous. -/
theorem PlaneDrawing.continuous_edgeParam (D : PlaneDrawing G) (e : G.edgeSet) :
    Continuous (D.edgeParam e) := by
  exact (PiLp.continuous_toLp 2 _).comp
    ((D.edge_continuous e).comp continuous_projIcc)

/-- The extension equals the original parametrization on its domain. -/
theorem PlaneDrawing.edgeParam_coe (D : PlaneDrawing G) (e : G.edgeSet) (t : I) :
    D.edgeParam e (t : ℝ) = WithLp.toLp 2 (D.edgePoint e t) := by
  simp [PlaneDrawing.edgeParam, Set.projIcc_of_mem zero_le_one t.2]

/-- Clamping leaves the first endpoint unchanged. -/
theorem PlaneDrawing.edgeParam_zero (D : PlaneDrawing G) (e : G.edgeSet) :
    D.edgeParam e 0 = D.point e.1.out.1 := by
  rw [PlaneDrawing.point, ← D.edge_zero e]
  exact D.edgeParam_coe e 0

/-- Clamping leaves the last endpoint unchanged. -/
theorem PlaneDrawing.edgeParam_one (D : PlaneDrawing G) (e : G.edgeSet) :
    D.edgeParam e 1 = D.point e.1.out.2 := by
  rw [PlaneDrawing.point, ← D.edge_one e]
  exact D.edgeParam_coe e 1

/-- An edge remains injective on the real closed unit interval. -/
theorem PlaneDrawing.edgeParam_injOn (D : PlaneDrawing G) (e : G.edgeSet) :
    Set.InjOn (D.edgeParam e) (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hsub : (⟨s, hs⟩ : I) = ⟨t, ht⟩ := by
    apply D.edge_injective e
    apply WithLp.toLp_injective 2
    simpa [PlaneDrawing.edgeParam, Set.projIcc_of_mem zero_le_one hs,
      Set.projIcc_of_mem zero_le_one ht] using hst
  exact congrArg Subtype.val hsub

end PlanarListColoring
