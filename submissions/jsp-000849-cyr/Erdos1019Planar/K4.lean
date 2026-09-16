import Erdos1019Planar.Planarity
import Erdos1019Planar.Separation

/-!
# A straight-line drawing of `K₄`

Vertices `0, 1, 2, 3` of `K₄` are placed at `(0,0)`, `(4,0)`, `(0,4)` and `(1,1)`: an outer
triangle with the fourth vertex inside.  Every pair of disjoint edges is separated by one of the
functionals `y`, `x`, `4 - x - y`, and every two adjacent edges are non-collinear, so they
meet only at their common endpoint.
-/

open Set

/-- The positions of the four vertices of `K₄`. -/
def k4Pos : Fin 4 → ℝ × ℝ
  | 0 => (0, 0)
  | 1 => (4, 0)
  | 2 => (0, 4)
  | 3 => (1, 1)

/-- Every edge `{u, v}` of the drawing lies on an affine line missing the two other vertices:
`y`, `x`, `4 - x - y` for the sides of the outer triangle and `x - y`, `x + 3y - 4`,
`3x + y - 4` for the edges through the inner vertex. -/
private lemma exists_lineFun_edge (u v : Fin 4) (huv : u ≠ v) :
    ∃ a b c : ℝ, lineFun a b c (k4Pos u) = 0 ∧ lineFun a b c (k4Pos v) = 0 ∧
      ∀ w : Fin 4, w ≠ u → w ≠ v → lineFun a b c (k4Pos w) ≠ 0 := by
  fin_cases u <;> fin_cases v <;>
    first
    | exact absurd rfl huv
    | (refine ⟨0, 1, 0, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨1, 0, 0, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨-1, -1, 4, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨1, -1, 0, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨1, 3, -4, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos] <;> done)
    | (refine ⟨3, 1, -4, ?_, ?_, fun w ↦ ?_⟩ <;> try fin_cases w
       all_goals norm_num [lineFun, k4Pos])

/-- Two vertex-disjoint edges of the drawing have disjoint segments: one of `y`, `x`,
`4 - x - y` vanishes on one of them and is positive on the other. -/
private lemma disjoint_segment_k4Pos {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Disjoint (segment ℝ (k4Pos a) (k4Pos b)) (segment ℝ (k4Pos c) (k4Pos d)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd rfl hab
    | exact absurd rfl hcd
    | exact absurd rfl hac
    | exact absurd rfl had
    | exact absurd rfl hbc
    | exact absurd rfl hbd
    | (refine segment_disjoint_of_pos_of_nonpos (a := 0) (b := 1) (c := 0) ?_ ?_ ?_ ?_ <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine (segment_disjoint_of_pos_of_nonpos (a := 0) (b := 1) (c := 0) ?_ ?_ ?_ ?_).symm <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine segment_disjoint_of_pos_of_nonpos (a := 1) (b := 0) (c := 0) ?_ ?_ ?_ ?_ <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine (segment_disjoint_of_pos_of_nonpos (a := 1) (b := 0) (c := 0) ?_ ?_ ?_ ?_).symm <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine segment_disjoint_of_pos_of_nonpos (a := -1) (b := -1) (c := 4) ?_ ?_ ?_ ?_ <;>
        norm_num [lineFun, k4Pos] <;> done)
    | (refine (segment_disjoint_of_pos_of_nonpos (a := -1) (b := -1) (c := 4) ?_ ?_ ?_ ?_).symm <;>
        norm_num [lineFun, k4Pos])

/-- If `z` lies on the segments of the edges `{v, u}` and `{c, d}`, where `v` is an endpoint of
`{c, d}` and `u` is not, then `z` is the position of the common vertex `v`. -/
private lemma eq_k4Pos_of_mem_segment {v u c d : Fin 4} {z : ℝ × ℝ} (hcd : c ≠ d)
    (hv : v = c ∨ v = d) (huc : u ≠ c) (hud : u ≠ d) (hz1 : z ∈ segment ℝ (k4Pos v) (k4Pos u))
    (hz2 : z ∈ segment ℝ (k4Pos c) (k4Pos d)) : z = k4Pos v := by
  obtain ⟨a, b, e, hc, hd, hoff⟩ := exists_lineFun_edge c d hcd
  have hv0 : lineFun a b e (k4Pos v) = 0 := by rcases hv with rfl | rfl <;> assumption
  exact segment_inter_segment_subset_singleton_of_ne_zero hv0 (hoff u huc hud) hc hd ⟨hz1, hz2⟩

/-- The complete graph on four vertices has a straight-line plane drawing. -/
theorem top_four_isStraightLineDrawing :
    (⊤ : SimpleGraph (Fin 4)).IsStraightLineDrawing k4Pos := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h
    fin_cases u <;> fin_cases v <;> first | rfl | norm_num [k4Pos, Prod.ext_iff] at h
  · intro u v w huv hw
    rw [SimpleGraph.top_adj] at huv
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨a, b, c, hu, hv, hoff⟩ := exists_lineFun_edge u v huv
    exact notMem_segment_of_ne_zero (hoff w hne.1 hne.2) hu hv hw
  · intro a b c d hab hcd hne z ⟨hz1, hz2⟩
    rw [SimpleGraph.top_adj] at hab hcd
    by_cases h : a = c ∨ a = d ∨ b = c ∨ b = d
    · rcases h with rfl | rfl | rfl | rfl
      · have hbd : b ≠ d := fun h ↦ hne (by rw [h])
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inl rfl) hab.symm hbd hz1 hz2).symm⟩
        simp
      · have hbc : b ≠ c := fun h ↦ hne (by rw [h]; exact Sym2.eq_swap)
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inr rfl) hbc hab.symm hz1 hz2).symm⟩
        simp
      · rw [segment_symm] at hz1
        have had : a ≠ d := fun h ↦ hne (by rw [h]; exact Sym2.eq_swap)
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inl rfl) hab had hz1 hz2).symm⟩
        simp
      · rw [segment_symm] at hz1
        have hac : a ≠ c := fun h ↦ hne (by rw [h])
        refine ⟨_, ?_, (eq_k4Pos_of_mem_segment hcd (Or.inr rfl) hac hab hz1 hz2).symm⟩
        simp
    · simp only [not_or] at h
      obtain ⟨hac, had, hbc, hbd⟩ := h
      exact absurd hz2 (disjoint_left.1 (disjoint_segment_k4Pos hab hcd hac had hbc hbd) hz1)
