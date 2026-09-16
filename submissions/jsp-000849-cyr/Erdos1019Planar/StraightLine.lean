import Erdos1019Planar.Planarity

/-!
# Straight-line drawings are plane drawings

A straight-line drawing (`SimpleGraph.IsStraightLineDrawing`) yields a plane drawing whose
arcs are the closed segments between the endpoint positions.  The Jordan arc of an edge is the
affine parametrization `t ↦ (1 - t) • pos u + t • pos v` of `[0, 1]`, which is continuous and
injective because `pos u ≠ pos v`.
-/

open Set

namespace SimpleGraph

/-- A straight-line drawing gives a plane drawing, hence planarity. -/
theorem IsPlanar.of_isStraightLineDrawing {V : Type*} {G : SimpleGraph V} {pos : V → ℝ × ℝ}
    (h : G.IsStraightLineDrawing pos) : G.IsPlanar := by
  obtain ⟨hinj, hvert, hcross⟩ := h
  refine ⟨⟨pos, hinj, Sym2.lift ⟨fun u v ↦ segment ℝ (pos u) (pos v),
    fun u v ↦ segment_symm ℝ (pos u) (pos v)⟩, ?_, ?_, ?_⟩⟩
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      rw [mem_edgeSet] at he
      refine ⟨u, v, rfl, fun t ↦ (1 - t) • pos u + t • pos v, ?_, ?_, by simp, by simp, ?_⟩
      · exact (by fun_prop : Continuous fun t : ℝ ↦ (1 - t) • pos u + t • pos v).continuousOn
      · intro s _ t _ hst
        have hne : pos v - pos u ≠ 0 := sub_ne_zero.mpr fun h' ↦ he.ne (hinj h').symm
        have hzero : (s - t) • (pos v - pos u) = 0 := by
          linear_combination (norm := module) hst
        rcases smul_eq_zero.mp hzero with hst' | hst'
        · exact sub_eq_zero.mp hst'
        · exact absurd hst' hne
      · exact segment_eq_image ℝ (pos u) (pos v)
  · intro e he w hw
    induction e using Sym2.inductionOn with
    | hf u v =>
      rw [mem_edgeSet] at he
      exact Sym2.mem_iff.mpr (hvert u v w he hw)
  · intro e he f hf hef
    induction e, f using Sym2.inductionOn₂ with
    | hf a b c d =>
      rw [mem_edgeSet] at he hf
      exact hcross a b c d he hf hef

end SimpleGraph
