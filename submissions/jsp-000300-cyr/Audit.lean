import Proof

open Erdos364

#print axioms Erdos364.exists_consecutive_powerful_gt
#print axioms Erdos364.infinite_consecutive_powerful
#print axioms Erdos364.exists_pell_gt
#print axioms Erdos364.powerful_eight_mul_sq
#print axioms Erdos364.powerful_sq
#print axioms Erdos364.not_four_consecutive_powerful

example : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Powerful n ∧ Powerful (n + 1) :=
  Erdos364.exists_consecutive_powerful_gt
example : {n : ℕ | Powerful n ∧ Powerful (n + 1)}.Infinite := Erdos364.infinite_consecutive_powerful
example : ∀ N : ℕ, ∃ x y : ℕ, N < y ∧ x ^ 2 = 8 * y ^ 2 + 1 := Erdos364.exists_pell_gt
example : ∀ y : ℕ, Powerful (8 * y ^ 2) := Erdos364.powerful_eight_mul_sq
example : ∀ x : ℕ, Powerful (x ^ 2) := Erdos364.powerful_sq
example : ∀ n : ℕ, ¬ (Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2) ∧ Powerful (n + 3)) :=
  Erdos364.not_four_consecutive_powerful

#print Erdos364.Powerful
