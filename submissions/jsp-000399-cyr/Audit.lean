import Proof

open Erdos494

#print axioms Erdos494.card_divisible_by_prime_gt_k
#print axioms Erdos494.k_eq_2_card_not_pow_two
#print axioms Erdos494.card_divisible_by_prime_gt_k_explicit
#print axioms Erdos494.k_eq_2_card_not_pow_two_explicit

example : ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card :=
  Erdos494.card_divisible_by_prime_gt_k

example : ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card :=
  Erdos494.k_eq_2_card_not_pow_two

#print sumMultiset
#print Erdos494Unique
