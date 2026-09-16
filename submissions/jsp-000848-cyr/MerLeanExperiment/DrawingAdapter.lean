import MerLeanExperiment.EdgeIncidence

open scoped Graph
open Schoenflies

namespace PlanarListColoring

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Real-plane edge curves indexed by the ambient edge-name type.
Names which are not edges are assigned a dummy value outside all drawing requirements. -/
noncomputable def PlaneDrawing.drawing (D : PlaneDrawing G) (e : Sym2 V)
    (t : ℝ) : Plane := by
  classical
  exact if he : e ∈ G.edgeSet then D.edgeParam ⟨e, he⟩ t else 0

/-- On genuine edges, the ambient drawing agrees with the original edge curve. -/
theorem PlaneDrawing.drawing_of_mem (D : PlaneDrawing G) (e : Sym2 V)
    (he : e ∈ G.edgeSet) (t : ℝ) :
    D.drawing e t = D.edgeParam ⟨e, he⟩ t := by
  simp [PlaneDrawing.drawing, he]

/-- The canonical ordered representatives of an edge give a link in the relabeled graph. -/
private theorem PlaneDrawing.planeGraph_isLink_out (D : PlaneDrawing G) (e : Sym2 V)
    (he : e ∈ G.edgeSet) :
    D.planeGraph.IsLink e (D.point e.out.1) (D.point e.out.2) := by
  apply Graph.IsLink.map D.point
  exact ⟨e.out_eq.symm, he⟩

/-- An ordinary crossing-free drawing realizes the standard plane-graph interface. -/
theorem PlaneDrawing.isDrawing (D : PlaneDrawing G) :
    Graph.IsDrawing D.planeGraph D.drawing := by
  refine { edge_param := ?_, vertex_mem_edgeArc := ?_, edge_inter := ?_ }
  · intro e he
    have hdrawing : D.drawing e = D.edgeParam ⟨e, he⟩ :=
      funext (D.drawing_of_mem e he)
    rw [hdrawing]
    have hl := D.planeGraph_isLink_out e he
    refine ⟨(D.continuous_edgeParam ⟨e, he⟩).continuousOn,
      D.edgeParam_injOn ⟨e, he⟩, ?_⟩
    simpa [D.edgeParam_zero ⟨e, he⟩, D.edgeParam_one ⟨e, he⟩] using hl
  · intro e x y v hl hv hve
    rw [D.planeGraph_vertexSet] at hv
    obtain ⟨w, rfl⟩ := hv
    obtain ⟨t, ht, htw⟩ := hve
    have hpoint : D.edgeParam ⟨e, hl.edge_mem⟩ t = D.point w := by
      rw [← D.drawing_of_mem e hl.edge_mem]
      exact htw
    have hw := D.edgeParam_eq_point ⟨e, hl.edge_mem⟩ ⟨t, ht⟩ w hpoint
    rcases hl.eq_and_eq_or_eq_and_eq
        (D.planeGraph_isLink_out e hl.edge_mem) with hxy | hxy
    · rcases hxy with ⟨rfl, rfl⟩
      exact hw.imp (congrArg D.point) (congrArg D.point)
    · rcases hxy with ⟨rfl, rfl⟩
      exact hw.symm.imp (congrArg D.point) (congrArg D.point)
  · intro e f he hf hef p hpe hpf
    obtain ⟨s, hs, hsp⟩ := hpe
    obtain ⟨t, ht, htp⟩ := hpf
    let ee : G.edgeSet := ⟨e, he⟩
    let ff : G.edgeSet := ⟨f, hf⟩
    have hef' : ee ≠ ff := by
      intro h
      exact hef (congrArg Subtype.val h)
    have hinter : D.edgeParam ee s = D.edgeParam ff t := by
      rw [← D.drawing_of_mem e he, ← D.drawing_of_mem f hf]
      exact hsp.trans htp.symm
    obtain ⟨v, hev⟩ := D.edgeParam_inter_vertex ee ff hef' ⟨s, hs⟩ ⟨t, ht⟩ hinter
    have hpv : p = D.point v := hsp.symm.trans <| (D.drawing_of_mem e he s).trans hev
    have hfv : D.edgeParam ff t = D.point v := hinter.symm.trans hev
    have he_end := D.edgeParam_eq_point ee ⟨s, hs⟩ v hev
    have hf_end := D.edgeParam_eq_point ff ⟨t, ht⟩ v hfv
    rw [hpv]
    refine ⟨?_, ?_, ?_⟩
    · rw [D.planeGraph_vertexSet]
      exact ⟨v, rfl⟩
    · rcases he_end with rfl | rfl
      · exact (D.planeGraph_isLink_out e he).inc_left
      · exact (D.planeGraph_isLink_out e he).inc_right
    · rcases hf_end with rfl | rfl
      · exact (D.planeGraph_isLink_out f hf).inc_left
      · exact (D.planeGraph_isLink_out f hf).inc_right

end PlanarListColoring
