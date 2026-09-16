import Proof

#print axioms powerful_pair_witness
#print axioms consecutive_powerful_not_always_square

example : 0 < (12167 : ℕ) ∧
    (∀ p : ℕ, p.Prime → p ∣ 12167 → p ^ 2 ∣ 12167) ∧
    (∀ p : ℕ, p.Prime → p ∣ 12168 → p ^ 2 ∣ 12168) ∧
    ¬ IsSquare (12167 : ℕ) ∧ ¬ IsSquare (12168 : ℕ) := powerful_pair_witness

example : ¬ (∀ n : ℕ, 0 < n →
    (∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n) →
    (∀ p : ℕ, p.Prime → p ∣ n + 1 → p ^ 2 ∣ n + 1) →
    IsSquare n ∨ IsSquare (n + 1)) := consecutive_powerful_not_always_square
