import Proof

open Erdos348

#print axioms Erdos348.strongPairs_ge_two_eq_empty
#print axioms Erdos348.exists_infinite_removal
#print axioms Erdos348.exists_removal_card

example : {p : ℕ × ℕ | 2 ≤ p.1 ∧ p.1 < p.2 ∧ ∃ a : ℕ → ℕ, Monotone a ∧ (∀ i, 1 ≤ a i) ∧
    RobustlyComplete a p.1 ∧ ∀ S : Finset ℕ, S.card = p.2 → ¬ Complete a (↑S : Set ℕ)ᶜ} = ∅ :=
  Erdos348.strongPairs_ge_two_eq_empty

example : ∀ (a : ℕ → ℕ), Monotone a → (∀ i, 1 ≤ a i) → ∀ m, 2 ≤ m → RobustlyComplete a m →
    ∃ R : Set ℕ, R.Infinite ∧ Complete a Rᶜ :=
  Erdos348.exists_infinite_removal

example : ∀ (a : ℕ → ℕ), Monotone a → (∀ i, 1 ≤ a i) → ∀ m, 2 ≤ m → RobustlyComplete a m →
    ∀ n, ∃ S : Finset ℕ, S.card = n ∧ Complete a (↑S : Set ℕ)ᶜ :=
  Erdos348.exists_removal_card

#print Erdos348.Complete
#print Erdos348.RobustlyComplete
