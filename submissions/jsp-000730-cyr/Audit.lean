import Erdos879UpperBound

#print axioms erdos_879_upper_bound_closed
#print axioms erdos_879_upper_bound
#print axioms sum_lt_H_of_isAdmissible
#print axioms G_H_eval

/-- Erdős #879, the elementary Erdős–van Lint upper bound `G(n) < H(n)` for all `n ≥ 4`. -/
example (n : ℕ) (hn : 4 ≤ n) : G n < H n := erdos_879_upper_bound n hn

/-- The definitions unfold as intended. -/
example (S : Finset ℕ) : IsAdmissible S ↔ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b := Iff.rfl
example (n : ℕ) : H n = ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, p + n * Nat.primeCounting (Nat.sqrt n) := rfl
example : G 4 = 8 ∧ H 4 = 9 := G_H_eval
