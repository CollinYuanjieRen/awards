import Erdos1019Planar.Planarity
import Erdos1019Planar.Simonovits
import Erdos1019Planar.StraightLine
import Erdos1019Planar.K4
import Erdos1019Planar.Bipyramid

/-!
# Intended-model adapters

Concrete instances of the objects quantified over in `erdos_1019_saturated_planar`:

* `fourCliqueGraph`, a finite simple graph satisfying the edge-count hypothesis of the theorem
  (`n = 4`, `⌊16/4⌋ + ⌊5/2⌋ = 6` edges), witnessing that the hypothesis is satisfiable;
* `bipyramidGraph_saturated_planar`, showing that every bipyramid is a saturated planar graph
  on more than three vertices in the sense of the theorem's conclusion.

These are consistency witnesses for the audit; the main theorem does not depend on them.
-/

open Finset
open scoped SimpleGraph

/-- The complete graph on four vertices, a concrete instance of the theorem's hypothesis. -/
def fourCliqueGraph : SimpleGraph (Fin 4) :=
  ⊤

/-- `fourCliqueGraph` has exactly `⌊4²/4⌋ + ⌊(4+1)/2⌋ = 6` edges. -/
theorem fourCliqueGraph_edgeSet_ncard :
    fourCliqueGraph.edgeSet.ncard =
      Fintype.card (Fin 4) * Fintype.card (Fin 4) / 4 + (Fintype.card (Fin 4) + 1) / 2 := by
  rw [fourCliqueGraph, Erdos1019.edgeSet_ncard_eq_card_edgeFinset,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp [Nat.choose]

/-- Every bipyramid over an `l`-cycle, `l ≥ 3`, is a saturated planar graph on more than three
vertices: planar, with `3m - 6` edges on `m = l + 2 > 3` vertices. -/
theorem bipyramidGraph_saturated_planar (l : ℕ) (hl : 3 ≤ l) :
    (Erdos1019.bipyramidGraph l).IsPlanar ∧ 3 < Fintype.card (Fin l ⊕ Bool) ∧
      (Erdos1019.bipyramidGraph l).edgeSet.ncard = 3 * Fintype.card (Fin l ⊕ Bool) - 6 := by
  refine ⟨SimpleGraph.IsPlanar.of_isStraightLineDrawing
    (Bipyramid.bipyramidGraph_isStraightLineDrawing l hl), ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
    omega
  · rw [Erdos1019.edgeSet_ncard_eq_card_edgeFinset, Erdos1019.bipyramidGraph_card_edges hl]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
    omega
