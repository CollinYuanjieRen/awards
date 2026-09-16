import Proof

open Erdos1011

#print axioms Erdos1011.f3_eq
#print axioms Erdos1011.edges_le_of_cliqueFree_of_not_colorable
#print axioms Erdos1011.exists_extremal

example : ∀ n : ℕ, 5 ≤ n → f3 n = (n - 1) ^ 2 / 4 + 2 := Erdos1011.f3_eq

example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 → ¬ G.Colorable 2 →
    G.edgeSet.ncard ≤ (n - 1) ^ 2 / 4 + 1 :=
  Erdos1011.edges_le_of_cliqueFree_of_not_colorable

example : ∀ n : ℕ, 5 ≤ n → ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ ¬ G.Colorable 2 ∧
    G.edgeSet.ncard = (n - 1) ^ 2 / 4 + 1 :=
  Erdos1011.exists_extremal

#print Erdos1011.f3
