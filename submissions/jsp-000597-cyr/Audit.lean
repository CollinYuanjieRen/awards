import Erdos729LogBound

open Nat

#print axioms erdos_729_erdos_bound_closed
#print axioms Erdos729.erdos_729_erdos_bound

/-- Erdős #729: `a! b! ∣ n!` implies `a + b ≤ n + 2 log₂ n + 2`. -/
example (a b n : ℕ) (h : a ! * b ! ∣ n !) : a + b ≤ n + 2 * Nat.log 2 n + 2 :=
  Erdos729.add_le_of_factorial_mul_factorial_dvd a b n h
