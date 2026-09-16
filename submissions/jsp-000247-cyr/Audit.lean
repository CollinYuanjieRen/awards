import Erdos291ii

#print axioms erdos_291_part_ii
#print axioms erdos_291_part_ii_not_finite

/-- Erdős Problem #291, part (ii), in the formal-conjectures shape. -/
example : {n : ℕ | Nat.gcd (a n) (L n) > 1}.Infinite :=
  erdos_291_part_ii

/-- The definitions agree with the formal-conjectures file. -/
example : L 4 = 12 ∧ a 4 = 25 := ⟨L_a_eval.2.2.2.1, L_a_eval.2.2.2.2.2.2.2⟩
