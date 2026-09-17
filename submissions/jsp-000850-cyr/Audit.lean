import Proof

open Erdos1020

#print axioms Erdos1020.not_exists_lt_and_ne
#print axioms Erdos1020.f_eq_choose_of_lt
#print axioms Erdos1020.not_hasMatching_of_lt
#print axioms Erdos1020.f_le_choose
#print axioms Erdos1020.card_le_f

example : ∀ n r k : ℕ, ¬ (n < r * k ∧ f n r k ≠ n.choose r) := Erdos1020.not_exists_lt_and_ne
example : ∀ n r k : ℕ, n < r * k → f n r k = n.choose r := Erdos1020.f_eq_choose_of_lt
example : ∀ (n r k : ℕ) (H : Finset (Finset (Fin n))), IsUniform r H → n < r * k →
    ¬ HasMatching k H := Erdos1020.not_hasMatching_of_lt
example : ∀ n r k : ℕ, f n r k ≤ n.choose r := Erdos1020.f_le_choose
example : ∀ (n r k : ℕ) (H : Finset (Finset (Fin n))), IsUniform r H → ¬ HasMatching k H →
    H.card ≤ f n r k := Erdos1020.card_le_f

#print Erdos1020.IsUniform
#print Erdos1020.HasMatching
#print Erdos1020.f
