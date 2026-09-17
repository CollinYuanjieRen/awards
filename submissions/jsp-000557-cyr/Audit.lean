import Proof

open Erdos685

#print axioms Erdos685.choose_le_pow_card_primeFactors
#print axioms Erdos685.log_choose_le_card_mul_log
#print axioms Erdos685.log_choose_div_log_le_card
#print axioms Erdos685.strict_fails_two_one
#print axioms Erdos685.pow_factorization_choose_le'

example : ∀ n k : ℕ, n.choose k ≤ n ^ (n.choose k).primeFactors.card :=
  Erdos685.choose_le_pow_card_primeFactors
example : ∀ n k : ℕ, Real.log (n.choose k) ≤ ((n.choose k).primeFactors.card : ℝ) * Real.log n :=
  Erdos685.log_choose_le_card_mul_log
example : ∀ n k : ℕ, 2 ≤ n →
    Real.log (n.choose k) / Real.log n ≤ ((n.choose k).primeFactors.card : ℝ) :=
  Erdos685.log_choose_div_log_le_card
example : Real.log (Nat.choose 2 1) / Real.log 2 = ((Nat.choose 2 1).primeFactors.card : ℝ) :=
  Erdos685.strict_fails_two_one
example : ∀ n k p : ℕ, 0 < n → p ^ (n.choose k).factorization p ≤ n :=
  Erdos685.pow_factorization_choose_le'

#print Nat.primeFactors
#print Nat.choose
