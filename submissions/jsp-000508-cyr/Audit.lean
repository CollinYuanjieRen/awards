import Proof

open Erdos627

#print axioms Erdos627.exists_cliqueFree_chromatic
#print axioms Erdos627.exists_cliqueNum_two_chromatic
#print axioms Erdos627.shiftGraph_cliqueFree
#print axioms Erdos627.shiftGraph_chromaticNumber
#print axioms Erdos627.shiftGraph_cliqueNum

example : ∀ k : ℕ, ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞) := Erdos627.exists_cliqueFree_chromatic
example : ∀ k : ℕ, 2 ≤ k → ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    G.CliqueFree 3 ∧ (∃ u v, G.Adj u v) ∧ G.chromaticNumber = (k : ℕ∞) :=
  Erdos627.exists_cliqueNum_two_chromatic
example : ∀ N : ℕ, (shiftGraph N).CliqueFree 3 := Erdos627.shiftGraph_cliqueFree
example : ∀ k : ℕ, (shiftGraph (2 ^ k)).chromaticNumber = (k : ℕ∞) :=
  Erdos627.shiftGraph_chromaticNumber
example : ∀ k : ℕ, 2 ≤ k → (shiftGraph (2 ^ k)).cliqueNum = 2 := Erdos627.shiftGraph_cliqueNum

#print Erdos627.ShiftVertex
#print Erdos627.shiftGraph
