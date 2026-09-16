import Erdos23BlowupC5

open SimpleGraph

#print axioms erdos_23_n5_tight
#print axioms blowupC5_tight
#print axioms blowupC5_cliqueFree

open scoped Classical in
/-- Erdős #23 tightness at 25 vertices (formal-conjectures `erdos_23.variants.n5_tight`). -/
example : ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
    H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card := erdos_23_n5_tight

/-- The blow-up is the formal-conjectures graph. -/
example (n : ℕ) (x y : ZMod 5 × Fin n) :
    (blowupC5 n).Adj x y ↔ x ≠ y ∧ ((x.1 + 1 = y.1 ∨ y.1 + 1 = x.1) ∨ (y.1 + 1 = x.1 ∨ x.1 + 1 = y.1)) := by
  simp [blowupC5, SimpleGraph.fromRel_adj]
