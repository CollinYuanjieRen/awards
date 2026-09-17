import Proof

open Erdos828

#print axioms Erdos828.totient_dvd_iff
#print axioms Erdos828.totient_dvd_two_pow_mul_three_pow
#print axioms Erdos828.exists_eq_two_pow_mul_three_pow_of_totient_dvd
#print axioms Erdos828.not_totient_dvd_three_pow

example : ∀ n : ℕ, Nat.totient n ∣ n ↔ n ≤ 1 ∨ ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b :=
  Erdos828.totient_dvd_iff
example : ∀ a b : ℕ, 0 < a → Nat.totient (2 ^ a * 3 ^ b) ∣ 2 ^ a * 3 ^ b :=
  Erdos828.totient_dvd_two_pow_mul_three_pow
example : ∀ n : ℕ, 2 ≤ n → Nat.totient n ∣ n → ∃ a b : ℕ, 0 < a ∧ n = 2 ^ a * 3 ^ b :=
  Erdos828.exists_eq_two_pow_mul_three_pow_of_totient_dvd
example : ∀ b : ℕ, 0 < b → ¬ Nat.totient (3 ^ b) ∣ 3 ^ b := Erdos828.not_totient_dvd_three_pow

#print Nat.totient
