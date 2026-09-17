import Mathlib

/-!
# Erdős Problem #915 (JSP-000759): frozen definitions and root faces

Bollobás–Erdős (1962): let `G` be a graph with `1 + n(m-1)` vertices and `1 + n·C(m,2)` edges.
Must `G` contain two vertices connected by `m` disjoint paths?  The word "disjoint" may mean
internally vertex-disjoint or edge-disjoint (erdosproblems.com/915).  The resolved answer is:
* vertex-disjoint reading: yes for `m = 2, 3, 4` (trivial; Bártfai 1960; Bollobás 1966),
  no for every `m ≥ 5` (Leonard 1973 / Sørensen–Thomassen 1974; Mader 1973);
* edge-disjoint reading: yes for every `m ≥ 2` (Mader 1973), and in general
  `ℓ_m(n) = ⌊m(n-1)/2⌋ + 1`.
-/

namespace Erdos915

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two `u`–`v` walks are *internally disjoint*: every vertex they share is an endpoint. -/
def InternallyDisjoint {u v : V} (p q : G.Walk u v) : Prop :=
  ∀ w ∈ p.support, w ∈ q.support → w = u ∨ w = v

/-- `G` has two distinct vertices joined by `m` pairwise internally vertex-disjoint paths
(an `m`-rail in the terminology of Sørensen–Thomassen). -/
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

/-! ## Root faces (stated with `sorry` here only as the frozen interface; proved elsewhere). -/

/-- The Bollobás–Erdős conjecture is true for `m = 2, 3, 4` (vertex-disjoint reading). -/
theorem vertex_rails_of_le_four {m n : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hn : 1 ≤ n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (m - 1)) (hE : G.edgeSet.ncard = 1 + n * m.choose 2) :
    HasVertexRails G m := by
  sorry

/-- The Bollobás–Erdős conjecture is false for every `m ≥ 5` (vertex-disjoint reading). -/
theorem exists_no_vertex_rails_of_ge_five {m : ℕ} (hm : 5 ≤ m) :
    ∃ (n : ℕ) (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      1 ≤ n ∧ Fintype.card V = 1 + n * (m - 1) ∧ G.edgeSet.ncard = 1 + n * m.choose 2 ∧
        ¬ HasVertexRails G m := by
  sorry

/-- Mader (1973), Satz 1: for `N ≥ m`, more than `(m/2)(N-1) - ½(e₀ + ⋯ + e_{m-2})` edges force
`m` edge-disjoint paths.  (The side condition `m ≤ N` is in Mader's statement and is necessary:
`K₃` with `m = 5` violates the inequality-only form; erdosproblems.com omits it.) -/
theorem mader_edge_rails {m : ℕ} (hm : 2 ≤ m) {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hN : m ≤ Fintype.card V)
    (h : m * (Fintype.card V - 1) <
      2 * G.edgeSet.ncard + ∑ r ∈ Finset.range (m - 1), lowDegreeCount G r) :
    HasEdgeRails G m := by
  sorry

/-- The Bollobás–Erdős conjecture is true for every `m ≥ 2` under the edge-disjoint reading. -/
theorem edge_rails_of_bollobas_erdos {m n : ℕ} (hm2 : 2 ≤ m) (hn : 1 ≤ n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (m - 1)) (hE : G.edgeSet.ncard = 1 + n * m.choose 2) :
    HasEdgeRails G m := by
  sorry

/-- `ℓ_m(n) = ⌊m(n-1)/2⌋ + 1` for `2 ≤ m ≤ n` (Mader 1973, Korollar).  The side condition `m ≤ n`
is Mader's; for `n < m` the least-element set below is vacuous above `C(n,2)` and the printed
value is wrong (e.g. `m = 5`, `n = 3`). -/
theorem edgeRailNumber_eq (m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    IsLeast {k : ℕ | ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n → k ≤ G.edgeSet.ncard → HasEdgeRails G m}
      (m * (n - 1) / 2 + 1) := by
  sorry

end Erdos915
