import Proof

open Erdos181 SimpleGraph

#print axioms Erdos181.graphRamsey_hypercube_le
#print axioms Erdos181.graphRamsey_hypercube_le_R
#print axioms Erdos181.graphRamsey_le_R
#print axioms Erdos181.graphRamseyProp_ramsey
#print axioms Erdos181.isContained_of_not_cliqueFree
#print axioms Erdos181.ramsey_diag_le_four_pow

example : ∀ n : ℕ, graphRamsey (hypercube n) ≤ 4 ^ (2 ^ n) :=
  Erdos181.graphRamsey_hypercube_le
example : ∀ n : ℕ, graphRamsey (hypercube n) ≤ R (2 ^ n) :=
  Erdos181.graphRamsey_hypercube_le_R
example : ∀ {V : Type} [Fintype V] (G : SimpleGraph V), graphRamsey G ≤ R (Fintype.card V) := by
  intro V _ G; exact Erdos181.graphRamsey_le_R G
example : ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    GraphRamseyProp (ramsey (Fintype.card V) (Fintype.card V)) G := by
  intro V _ G; exact Erdos181.graphRamseyProp_ramsey G
example : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) {N : ℕ} (R : SimpleGraph (Fin N)),
    ¬ R.CliqueFree (Fintype.card V) → G ⊑ R := by
  intro V _ G N R hR; exact Erdos181.isContained_of_not_cliqueFree G R hR
example : ∀ n : ℕ, ramsey n n ≤ 4 ^ n := Erdos181.ramsey_diag_le_four_pow

#print Erdos181.hypercube
#print Erdos181.GraphRamseyProp
#print Erdos181.graphRamsey
#print Erdos181.IsGood
#print Erdos181.RamseyProp
#print Erdos181.ramsey
#print Erdos181.R
