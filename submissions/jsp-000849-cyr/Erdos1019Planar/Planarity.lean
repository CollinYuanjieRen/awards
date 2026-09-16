import Mathlib

/-!
# Plane drawings of simple graphs

A plane drawing of a simple graph places the vertices at distinct points of `ℝ × ℝ` and
represents every edge by a Jordan arc (the injective continuous image of `[0, 1]`) joining the
images of its two endpoints, subject to the two usual non-crossing conditions: no vertex lies on
the arc of an edge that is not incident to it, and two distinct arcs meet only in the images of
their common endpoints.  A graph is planar when it admits such a drawing.

This is the ordinary topological notion; no combinatorial certificate is used.  Straight-line
drawings are a special case, see `SimpleGraph.IsStraightLineDrawing`.
-/

open Set

namespace SimpleGraph

/-- A plane drawing of `G`: an injective vertex placement and, for each edge, a Jordan arc
between the images of its endpoints, such that vertices avoid non-incident arcs and distinct
arcs meet only at images of shared endpoints. -/
structure PlaneDrawing {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex. -/
  pos : V → ℝ × ℝ
  /-- Distinct vertices are drawn at distinct points. -/
  pos_injective : Function.Injective pos
  /-- The point set representing each edge. -/
  arc : Sym2 V → Set (ℝ × ℝ)
  /-- Every edge is drawn as a Jordan arc from the image of one endpoint to the other. -/
  arc_isArc : ∀ e ∈ G.edgeSet, ∃ u v : V, e = s(u, v) ∧ ∃ γ : ℝ → ℝ × ℝ,
    ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ 0 = pos u ∧ γ 1 = pos v ∧
      arc e = γ '' Icc 0 1
  /-- A vertex lies on the arc of an edge only if it is an endpoint of that edge. -/
  vertex_mem_arc : ∀ e ∈ G.edgeSet, ∀ w : V, pos w ∈ arc e → w ∈ e
  /-- Two distinct arcs meet only in images of common endpoints. -/
  arc_inter_arc : ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f →
    arc e ∩ arc f ⊆ pos '' {w : V | w ∈ e ∧ w ∈ f}

/-- A graph is planar when it admits a plane drawing. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneDrawing G)

/-- The vertex placement `pos` is a straight-line plane drawing of `G`: positions are
distinct, no vertex lies on the closed segment of a non-incident edge, and the closed segments
of two distinct edges meet only in positions of common endpoints. -/
def IsStraightLineDrawing {V : Type*} (G : SimpleGraph V) (pos : V → ℝ × ℝ) : Prop :=
  Function.Injective pos ∧
    (∀ u v w : V, G.Adj u v → pos w ∈ segment ℝ (pos u) (pos v) → w = u ∨ w = v) ∧
    (∀ a b c d : V, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
      segment ℝ (pos a) (pos b) ∩ segment ℝ (pos c) (pos d) ⊆
        pos '' {w : V | w ∈ s(a, b) ∧ w ∈ s(c, d)})

end SimpleGraph
