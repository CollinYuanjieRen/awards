import Mathlib

/-! Definitions for Erdős #915 (JSP-000759); identical to the frozen `Target.lean`, without the
sorry-stated faces, so that proof modules can import only definitions. -/

namespace Erdos915

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two `u`–`v` walks are *internally disjoint*: every vertex they share is an endpoint. -/
def InternallyDisjoint {u v : V} (p q : G.Walk u v) : Prop :=
  ∀ w ∈ p.support, w ∈ q.support → w = u ∨ w = v

/-- `G` has two distinct vertices joined by `m` pairwise internally vertex-disjoint paths. -/
def HasVertexRails (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, u ≠ v ∧ ∃ p : Fin m → G.Walk u v,
    Function.Injective p ∧ (∀ i, (p i).IsPath) ∧
      ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j)

/-- `G` has two distinct vertices joined by `m` pairwise edge-disjoint paths. -/
def HasEdgeRails (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, u ≠ v ∧ ∃ p : Fin m → G.Walk u v,
    (∀ i, (p i).IsPath) ∧ ∀ i j, i ≠ j → ∀ e ∈ (p i).edges, e ∉ (p j).edges

/-- `e_r(G)`: the number of vertices of degree at most `r`. -/
def lowDegreeCount (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v ≤ r).card

end Erdos915
