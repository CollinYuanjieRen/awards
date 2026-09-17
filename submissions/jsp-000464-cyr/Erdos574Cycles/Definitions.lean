import Mathlib

/-!
# Erdős Problem 574: Turán numbers of an odd and an even cycle of adjacent lengths

Erdős and Simonovits asked whether, for `k ≥ 2`,
`ex(n; {C_{2k−1}, C_{2k}}) = (1 + o(1)) (n/2)^{1 + 1/k}`.
This is false: for `k = 3`, Lazebnik, Ustimenko and Woldar's graphs `D(3, q)` (bipartite, girth
8) give, after doubling the set of lines, bipartite `C₆`-free graphs on `3q³` vertices with `2q⁴`
edges, i.e. `(2/3^{4/3}) n^{4/3}` edges, exceeding `(n/2)^{4/3}` by a constant factor.

This file defines the extremal number of the pair `{C_{2k−1}, C_{2k}}`, the Erdős–Simonovits
claim, the incidence relation of `D(3, q)` over a field, and the doubled incidence graph.
-/

namespace Erdos574

open SimpleGraph Finset Filter Topology

open scoped Classical in
/-- The maximum number of edges of a simple graph on `n` vertices containing neither `C_{2k−1}` nor
`C_{2k}` (as subgraphs). -/
noncomputable def exOddEven (n k : ℕ) : ℕ :=
  sup {G : SimpleGraph (Fin n) | (cycleGraph (2 * k - 1)).Free G ∧ (cycleGraph (2 * k)).Free G}
    (fun G => #G.edgeFinset)

/-- The Erdős–Simonovits claim for the parameter `k`:
`ex(n; {C_{2k−1}, C_{2k}}) = (1 + o(1)) (n/2)^{1 + 1/k}`. -/
def Claim (k : ℕ) : Prop :=
  Tendsto (fun n : ℕ => (exOddEven n k : ℝ) / ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))) atTop (𝓝 1)

variable (F : Type*) [Field F]

/-- Incidence of the point `p = (p₁, p₁₁, p₁₂)` and the line `l = [l₁, l₁₁, l₁₂]` in `D(3, q)`:
`l₁₁ = p₁₁ + l₁ p₁` and `l₁₂ = p₁₂ + l₁₁ p₁`. -/
def Incid (p l : F × F × F) : Prop :=
  l.2.1 = p.2.1 + l.1 * p.1 ∧ l.2.2 = p.2.2 + l.2.1 * p.1

instance [DecidableEq F] (p l : F × F × F) : Decidable (Incid F p l) := by
  unfold Incid; infer_instance

/-- Vertices of the doubled incidence graph: the points, and two copies of the lines. -/
abbrev Vtx := (F × F × F) ⊕ ((F × F × F) ⊕ (F × F × F))

/-- Adjacency of the doubled incidence graph: a point is adjacent to each copy of every line
incident to it; there are no other edges. -/
def dAdj : Vtx F → Vtx F → Prop
  | Sum.inl p, Sum.inr (Sum.inl l) => Incid F p l
  | Sum.inl p, Sum.inr (Sum.inr l) => Incid F p l
  | Sum.inr (Sum.inl l), Sum.inl p => Incid F p l
  | Sum.inr (Sum.inr l), Sum.inl p => Incid F p l
  | _, _ => False

theorem dAdj_symm : ∀ u v, dAdj F u v → dAdj F v u := by
  intro u v h
  rcases u with p | l | l <;> rcases v with p' | l' | l' <;> simp_all [dAdj]

theorem dAdj_irrefl : ∀ u, ¬ dAdj F u u := by
  intro u
  rcases u with p | l | l <;> simp [dAdj]

/-- The doubled incidence graph of `D(3, q)`: `3q³` vertices, `2q⁴` edges, bipartite, `C₆`-free. -/
def doubled : SimpleGraph (Vtx F) where
  Adj := dAdj F
  symm := ⟨fun u v h => dAdj_symm F u v h⟩
  loopless := ⟨fun u h => dAdj_irrefl F u h⟩

instance [DecidableEq F] : DecidableRel (doubled F).Adj := by
  intro u v
  rcases u with p | l | l <;> rcases v with p' | l' | l' <;> simp only [doubled, dAdj] <;> infer_instance

end Erdos574
