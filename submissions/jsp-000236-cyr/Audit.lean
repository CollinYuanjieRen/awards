import Proof

open Erdos276

#print axioms Erdos276.exists_composite_lucasSequence
#print axioms Erdos276.vsemirnov_exists_proper_factor
#print axioms Erdos276.vsemirnov_coprime_succ
#print axioms Erdos276.vsemirnov_not_prime
#print axioms Erdos276.vsemirnov_no_common_divisor

example : ∃ a : ℕ → ℕ, IsLucasSequence a ∧ (∀ k, 1 < a k ∧ ¬ (a k).Prime) ∧ (∀ d, 2 ≤ d → ∃ k, ¬ d ∣ a k) :=
  Erdos276.exists_composite_lucasSequence

example : ∀ k, ∃ p, 1 < p ∧ p < vsemirnov k ∧ p ∣ vsemirnov k :=
  Erdos276.vsemirnov_exists_proper_factor

example : ∀ k, Nat.Coprime (vsemirnov k) (vsemirnov (k + 1)) :=
  Erdos276.vsemirnov_coprime_succ

#print Erdos276.IsLucasSequence
#print Erdos276.lucasPair
#print Erdos276.lucas
#print Erdos276.vsemirnov
