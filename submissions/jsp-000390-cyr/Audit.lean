import Erdos479KnownCases

#print axioms erdos_479_known_cases
#print axioms erdos_479_two_pow
#print axioms erdos_479_neg_one
#print axioms erdos_479_zero

/-- Erdős #479, the known cases, as a closed statement. -/
example : ¬ ∃ k : ℤ, (k = 0 ∨ k = -1 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) ∧
    { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Finite :=
  erdos_479_known_cases

/-- The formal-conjectures shape (`Erdos479.erdos_479` quantifies over `k ≠ 1` with this set) for
each known `k`. -/
example (i : ℕ) (hi : 1 ≤ i) : { n : ℕ | (2 : ℤ) ^ n ≡ 2 ^ i [ZMOD (n : ℤ)] }.Infinite :=
  erdos_479_two_pow i hi
example : { n : ℕ | (2 : ℤ) ^ n ≡ -1 [ZMOD (n : ℤ)] }.Infinite := erdos_479_neg_one
