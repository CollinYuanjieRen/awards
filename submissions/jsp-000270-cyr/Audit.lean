import Erdos324LowDeg

open Polynomial
open scoped Polynomial

#print axioms erdos_324_low_degree_and_quartic
#print axioms not_sidonPoly_of_natDegree_le_two
#print axioms not_sidonPoly_X_pow_four

/-- Erdős Problem #324, settled cases, in the formal-conjectures shape of `Erdos324.erdos_324`. -/
example : ¬ ∃ f : ℤ[X], (f.natDegree ≤ 2 ∨ f = X ^ 4) ∧
    {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ) :=
  erdos_324_low_degree_and_quartic

/-- Euler's collision behind the quartic case. -/
example : (59 : ℤ) ^ 4 + 158 ^ 4 = 133 ^ 4 + 134 ^ 4 := by norm_num
