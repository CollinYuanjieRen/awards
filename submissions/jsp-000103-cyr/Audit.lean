import Proof

open Erdos87 SimpleGraph

#print axioms Erdos87.not_exists_four_pow_mul_graphRamsey_le
#print axioms Erdos87.lt_graphRamsey_of_chromaticNumber
#print axioms Erdos87.R_lt_four_pow_mul_graphRamsey
#print axioms Erdos87.two_le_graphRamsey_of_adj
#print axioms Erdos87.exists_adj_of_two_le_chromaticNumber
#print axioms Erdos87.ramsey_diag_le_four_pow

example : ∀ n k : ℕ, ¬ ∃ G : SimpleGraph (Fin n), 2 ≤ k ∧ G.chromaticNumber = (k : ℕ∞) ∧
    4 ^ k * graphRamsey G ≤ R k :=
  Erdos87.not_exists_four_pow_mul_graphRamsey_le
example : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ), 2 ≤ k →
    G.chromaticNumber = (k : ℕ∞) → ∀ ε : ℝ, 3 / 4 ≤ ε → ε ≤ 1 →
    (1 - ε) ^ k * (R k : ℝ) < graphRamsey G := by
  intro V _ G k hk hG ε hε hε1; exact Erdos87.lt_graphRamsey_of_chromaticNumber G k hk hG ε hε hε1
example : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ), 2 ≤ k →
    G.chromaticNumber = (k : ℕ∞) → R k < 4 ^ k * graphRamsey G := by
  intro V _ G k hk hG; exact Erdos87.R_lt_four_pow_mul_graphRamsey G k hk hG
example : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) {u v : V}, G.Adj u v →
    2 ≤ graphRamsey G := by
  intro V _ G u v h; exact Erdos87.two_le_graphRamsey_of_adj G h
example : ∀ {V : Type} (G : SimpleGraph V), 2 ≤ G.chromaticNumber → ∃ u v : V, G.Adj u v := by
  intro V G h; exact Erdos87.exists_adj_of_two_le_chromaticNumber G h
example : ∀ n : ℕ, ramsey n n ≤ 4 ^ n := Erdos87.ramsey_diag_le_four_pow

#print Erdos87.GraphRamseyProp
#print Erdos87.graphRamsey
#print Erdos87.IsGood
#print Erdos87.RamseyProp
#print Erdos87.ramsey
#print Erdos87.R
