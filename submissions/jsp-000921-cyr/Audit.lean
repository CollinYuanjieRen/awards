import ErdosLewin23

#print axioms erdos_lewin_two_three

/-- Erdős–Lewin, base case `{2, 3}`: every natural number is representable. -/
example (n : ℕ) : Representable 3 2 n :=
  erdos_lewin_two_three n

/-- The predicate unfolds to a finite divisibility antichain of numbers `3 ^ k * 2 ^ l`. -/
example (n : ℕ) : ∃ s : Finset ℕ, (s : Set ℕ) ⊆ {m : ℕ | ∃ k l : ℕ, m = 3 ^ k * 2 ^ l} ∧
    IsAntichain (· ∣ ·) (s : Set ℕ) ∧ s.sum id = n :=
  erdos_lewin_two_three n
