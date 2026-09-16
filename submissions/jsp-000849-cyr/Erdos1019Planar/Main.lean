import Erdos1019Planar.Planarity
import Erdos1019Planar.Simonovits
import Erdos1019Planar.StraightLine
import Erdos1019Planar.K4
import Erdos1019Planar.Bipyramid

/-!
# Erdős Problem #1019 with genuine planarity

Erdős asked whether every graph on `n` vertices with `⌊n²/4⌋ + ⌊(n+1)/2⌋` edges contains a
saturated planar graph on more than three vertices, a saturated planar graph on `m` vertices
being a planar graph with `3m - 6` edges.  Simonovits proved that such a graph contains `K₄`
or a bipyramid `C_l + 2K₁`; that combinatorial theorem is `Erdos1019.erdos_1019_sharp`.  Here
planarity is the topological notion `SimpleGraph.IsPlanar` (a plane drawing by Jordan arcs).
-/

open Finset
open scoped SimpleGraph

/-- **Erdős Problem #1019** (Simonovits).  Every graph on `n ≥ 1` vertices with exactly
`⌊n²/4⌋ + ⌊(n+1)/2⌋` edges contains a saturated planar graph on more than three vertices: a
planar graph `H` on `m > 3` vertices with `3m - 6` edges, together with a copy of `H` in `G`.
The edge count of `G` is its `edgeSet.ncard`, so no decidability instance appears on the theorem
face; `n = Fintype.card V ≥ 1`. -/
theorem erdos_1019_saturated_planar {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V)
    (hE : G.edgeSet.ncard = Fintype.card V * Fintype.card V / 4 + (Fintype.card V + 1) / 2) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      H.IsPlanar ∧ 3 < Fintype.card W ∧ H.edgeSet.ncard = 3 * Fintype.card W - 6 ∧ H ⊑ G := by
  classical
  have hE' : #G.edgeFinset = Erdos1019.problemThreshold (Fintype.card V) := by
    rw [← Erdos1019.edgeSet_ncard_eq_card_edgeFinset]
    exact hE
  rcases Erdos1019.erdos_1019_sharp G hE' with h4 | ⟨l, hl, hb⟩
  · refine ⟨Fin 4, inferInstance, ⊤,
      SimpleGraph.IsPlanar.of_isStraightLineDrawing top_four_isStraightLineDrawing, by simp, ?_, h4⟩
    rw [Erdos1019.edgeSet_ncard_eq_card_edgeFinset,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp [Nat.choose]
  · refine ⟨Fin l ⊕ Bool, inferInstance, Erdos1019.bipyramidGraph l,
      SimpleGraph.IsPlanar.of_isStraightLineDrawing
        (Bipyramid.bipyramidGraph_isStraightLineDrawing l hl), ?_, ?_, hb⟩
    · simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
      omega
    · rw [Erdos1019.edgeSet_ncard_eq_card_edgeFinset, Erdos1019.bipyramidGraph_card_edges hl]
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
      omega

/-- Closed form of `erdos_1019_saturated_planar`, with no hypotheses on its face: there is no
graph on `n + 1 ≥ 1` vertices with `⌊(n+1)²/4⌋ + ⌊(n+2)/2⌋` edges that avoids every saturated
planar graph on more than three vertices.  Since every finite graph on `n + 1` vertices is
isomorphic to one on `Fin (n + 1)`, this is Erdős Problem #1019 as a single closed proposition. -/
theorem erdos_1019_saturated_planar_closed :
    ¬ ∃ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
      G.edgeSet.ncard = (n + 1) * (n + 1) / 4 + (n + 1 + 1) / 2 ∧
        ∀ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
          H.IsPlanar → 3 < Fintype.card W → H.edgeSet.ncard = 3 * Fintype.card W - 6 → ¬ H ⊑ G := by
  rintro ⟨n, G, hE, hno⟩
  obtain ⟨W, _, H, hP, hW, hc, hcopy⟩ :=
    erdos_1019_saturated_planar G (by simpa [Fintype.card_fin] using hE)
  exact hno W _ H hP hW hc hcopy
