import Erdos1019Planar.Planarity
import Erdos1019Planar.Simonovits
import Erdos1019Planar.BipyramidChords
import Erdos1019Planar.BipyramidSpokes

/-!
# The bipyramid has a straight-line plane drawing

Assembling the chord and spoke lemmas: every edge of `Erdos1019.bipyramidGraph l` is either an
equatorial edge (an edge of `cycleGraph l`) or a spoke, and the segment conditions of
`SimpleGraph.IsStraightLineDrawing` follow by case analysis, using the symmetry of segments and
of unordered pairs.
-/

open Set
open scoped SimpleGraph

namespace Bipyramid

/-- The crossing condition of `SimpleGraph.IsStraightLineDrawing` for one pair of edges. -/
def CrossOk (l : ℕ) (a b c d : Fin l ⊕ Bool) : Prop :=
  segment ℝ (pos l a) (pos l b) ∩ segment ℝ (pos l c) (pos l d) ⊆
    pos l '' {w : Fin l ⊕ Bool | w ∈ s(a, b) ∧ w ∈ s(c, d)}

theorem CrossOk.swap_left {l : ℕ} {a b c d : Fin l ⊕ Bool} (h : CrossOk l a b c d) :
    CrossOk l b a c d := by
  unfold CrossOk at h ⊢
  rw [segment_symm, Sym2.eq_swap]
  exact h

theorem CrossOk.swap_right {l : ℕ} {a b c d : Fin l ⊕ Bool} (h : CrossOk l a b c d) :
    CrossOk l a b d c := by
  unfold CrossOk at h ⊢
  rw [segment_symm ℝ (pos l d), Sym2.eq_swap (a := d)]
  exact h

theorem CrossOk.comm {l : ℕ} {a b c d : Fin l ⊕ Bool} (h : CrossOk l a b c d) :
    CrossOk l c d a b := by
  unfold CrossOk at h ⊢
  rw [Set.inter_comm]
  refine h.trans (Set.image_mono ?_)
  intro w hw
  exact ⟨hw.2, hw.1⟩

/-- Equatorial adjacency in the bipyramid is cycle adjacency. -/
theorem adj_inl_inl {l : ℕ} {i j : Fin l}
    (h : (Erdos1019.bipyramidGraph l).Adj (Sum.inl i) (Sum.inl j)) :
    (SimpleGraph.cycleGraph l).Adj i j := h

/-- The two apices are not adjacent. -/
theorem not_adj_inr_inr {l : ℕ} {b c : Bool}
    (h : (Erdos1019.bipyramidGraph l).Adj (Sum.inr b) (Sum.inr c)) : False := h

theorem crossOk_chord_chord (l : ℕ) (hl : 3 ≤ l) (i j k m : Fin l)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) (hkm : (SimpleGraph.cycleGraph l).Adj k m)
    (hne : s((Sum.inl i : Fin l ⊕ Bool), Sum.inl j) ≠ s((Sum.inl k : Fin l ⊕ Bool), Sum.inl m)) :
    CrossOk l (Sum.inl i) (Sum.inl j) (Sum.inl k) (Sum.inl m) := by
  refine chord_inter_chord l hl i j k m hij hkm ?_
  intro h
  apply hne
  have := congrArg (Sym2.map (Sum.inl : Fin l → Fin l ⊕ Bool)) h
  simpa using this

theorem crossOk_chord_spoke (l : ℕ) (hl : 3 ≤ l) (i j k : Fin l) (b : Bool)
    (hij : (SimpleGraph.cycleGraph l).Adj i j) :
    CrossOk l (Sum.inl i) (Sum.inl j) (Sum.inl k) (Sum.inr b) :=
  chord_inter_spoke l hl i j k b hij

theorem crossOk_spoke_spoke (l : ℕ) (hl : 3 ≤ l) (i k : Fin l) (b c : Bool)
    (hne : s((Sum.inl i : Fin l ⊕ Bool), Sum.inr b) ≠ s((Sum.inl k : Fin l ⊕ Bool), Sum.inr c)) :
    CrossOk l (Sum.inl i) (Sum.inr b) (Sum.inl k) (Sum.inr c) :=
  spoke_inter_spoke l hl i k b c hne

/-- The crossing condition for every pair of distinct edges of the bipyramid. -/
theorem crossOk_of_adj (l : ℕ) (hl : 3 ≤ l) (a b c d : Fin l ⊕ Bool)
    (hab : (Erdos1019.bipyramidGraph l).Adj a b) (hcd : (Erdos1019.bipyramidGraph l).Adj c d)
    (hne : s(a, b) ≠ s(c, d)) : CrossOk l a b c d := by
  rcases a with i | p <;> rcases b with j | q
  · -- first edge is a chord
    rcases c with k | r <;> rcases d with m | s
    · exact crossOk_chord_chord l hl i j k m hab hcd hne
    · exact crossOk_chord_spoke l hl i j k s hab
    · exact (crossOk_chord_spoke l hl i j m r hab).swap_right
    · exact (not_adj_inr_inr hcd).elim
  · -- first edge is a spoke `inl i — inr q`
    rcases c with k | r <;> rcases d with m | s
    · exact (crossOk_chord_spoke l hl k m i q hcd).comm
    · exact crossOk_spoke_spoke l hl i k q s hne
    · refine (crossOk_spoke_spoke l hl i m q r ?_).swap_right
      rwa [Sym2.eq_swap (a := (Sum.inr r : Fin l ⊕ Bool))] at hne
    · exact (not_adj_inr_inr hcd).elim
  · -- first edge is a spoke `inr p — inl j`
    rcases c with k | r <;> rcases d with m | s
    · exact ((crossOk_chord_spoke l hl k m j p hcd).comm).swap_left
    · refine (crossOk_spoke_spoke l hl j k p s ?_).swap_left
      rwa [Sym2.eq_swap (a := (Sum.inr p : Fin l ⊕ Bool))] at hne
    · refine ((crossOk_spoke_spoke l hl j m p r ?_).swap_left).swap_right
      rwa [Sym2.eq_swap (a := (Sum.inr p : Fin l ⊕ Bool)),
        Sym2.eq_swap (a := (Sum.inr r : Fin l ⊕ Bool))] at hne
    · exact (not_adj_inr_inr hcd).elim
  · exact (not_adj_inr_inr hab).elim

/-- No vertex lies on the segment of a non-incident edge of the bipyramid. -/
theorem vertex_mem_of_adj (l : ℕ) (hl : 3 ≤ l) (u v w : Fin l ⊕ Bool)
    (huv : (Erdos1019.bipyramidGraph l).Adj u v)
    (hw : pos l w ∈ segment ℝ (pos l u) (pos l v)) : w = u ∨ w = v := by
  rcases u with i | p <;> rcases v with j | q
  · exact vertex_mem_chord l hl i j huv w hw
  · exact vertex_mem_spoke l hl i q w hw
  · rw [segment_symm] at hw
    exact (vertex_mem_spoke l hl j p w hw).symm
  · exact (not_adj_inr_inr huv).elim

/-- For `l ≥ 3`, the bipyramid over the `l`-cycle has a straight-line plane drawing. -/
theorem bipyramidGraph_isStraightLineDrawing (l : ℕ) (hl : 3 ≤ l) :
    (Erdos1019.bipyramidGraph l).IsStraightLineDrawing (pos l) :=
  ⟨pos_injective l (by omega), fun u v w huv hw ↦ vertex_mem_of_adj l hl u v w huv hw,
    fun a b c d hab hcd hne ↦ crossOk_of_adj l hl a b c d hab hcd hne⟩

end Bipyramid
