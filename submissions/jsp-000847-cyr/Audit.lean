import Proof

open Erdos1017 SimpleGraph

#print axioms Erdos1017.sq_div_four_le_f
#print axioms Erdos1017.cliquePartitionNum_balancedBipartite
#print axioms Erdos1017.card_edgeFinset_balancedBipartite
#print axioms Erdos1017.cliquePartitionNum_eq_of_cliqueFree
#print axioms Erdos1017.cliquePartitionNum_le_card_edgeFinset
#print axioms Erdos1017.balancedBipartite_cliqueFree_three

example : ∀ n : ℕ, n ^ 2 / 4 ≤ f n (n ^ 2 / 4) := Erdos1017.sq_div_four_le_f
example : ∀ n : ℕ, cliquePartitionNum (balancedBipartite n) = n ^ 2 / 4 :=
  Erdos1017.cliquePartitionNum_balancedBipartite
example : ∀ n : ℕ, (balancedBipartite n).edgeFinset.card = n ^ 2 / 4 :=
  Erdos1017.card_edgeFinset_balancedBipartite
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → cliquePartitionNum G = G.edgeFinset.card := by
  intro V _ _ G _ h; exact Erdos1017.cliquePartitionNum_eq_of_cliqueFree G h
example : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    cliquePartitionNum G ≤ G.edgeFinset.card := by
  intro V _ _ G _; exact Erdos1017.cliquePartitionNum_le_card_edgeFinset G
example : ∀ n : ℕ, (balancedBipartite n).CliqueFree 3 := Erdos1017.balancedBipartite_cliqueFree_three

#print Erdos1017.edgesOf
#print Erdos1017.IsCliquePartition
#print Erdos1017.cliquePartitionNum
#print Erdos1017.f
#print Erdos1017.balancedBipartite
