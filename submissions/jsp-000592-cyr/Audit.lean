import Erdos724Ten

#print axioms erdos_724_two_mols_ten
#print axioms squareA_isLatinSquare
#print axioms squareB_isLatinSquare
#print axioms squareA_squareB_isOrthogonal

/-- Two mutually orthogonal Latin squares of order 10 exist (Euler's conjecture fails at 10). -/
example : ∃ S : Fin 2 → Fin 10 → Fin 10 → Fin 10, IsMOLS 2 S :=
  erdos_724_two_mols_ten

/-- The definitions unfold to the intended row/column and superposition conditions. -/
example {n : ℕ} (L : Fin n → Fin n → Fin n) :
    IsLatinSquare L ↔ (∀ i, Function.Injective (L i)) ∧ (∀ j, Function.Injective fun i ↦ L i j) :=
  Iff.rfl
