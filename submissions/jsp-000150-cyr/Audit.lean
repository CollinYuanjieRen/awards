import Proof

open Erdos151

#print axioms Erdos151.not_exists_triangleFree_gt
#print axioms Erdos151.cliqueTransversalNum_le_of_cliqueFree
#print axioms Erdos151.cliqueTransversalNum_le_card_sub_indepNum
#print axioms Erdos151.H_le_indepNum
#print axioms Erdos151.isCliqueTransversal_compl_of_isIndepSet

example : ∀ n : ℕ, ¬ ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ n - H n < cliqueTransversalNum G :=
  Erdos151.not_exists_triangleFree_gt
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 →
    cliqueTransversalNum G ≤ n - H n := by
  intro n G hG; exact Erdos151.cliqueTransversalNum_le_of_cliqueFree n G hG
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    cliqueTransversalNum G ≤ Fintype.card V - G.indepNum := by
  intro V _ _ G; exact Erdos151.cliqueTransversalNum_le_card_sub_indepNum G
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 → H n ≤ G.indepNum := by
  intro n G hG; exact Erdos151.H_le_indepNum n G hG
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    G.IsIndepSet (S : Set V) → IsCliqueTransversal G (Finset.univ \ S) := by
  intro V _ _ G S hS; exact Erdos151.isCliqueTransversal_compl_of_isIndepSet G S hS

#print Erdos151.IsCliqueTransversal
#print Erdos151.cliqueTransversalNum
#print Erdos151.H
