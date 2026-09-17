import Erdos894Colouring

#print axioms Erdos894.erdos_894
#print axioms Erdos894.erdos_894_nat
#print axioms Erdos894.erdos_894_closed
#print axioms Erdos894.exists_rotation_of_four_mul_le
#print axioms Erdos894.exists_split_of_isLacunary
#print axioms Erdos894.hasAvoidingColouring_of_rotations

/-- Erdős Problem 894 with every auxiliary definition unfolded: a lacunary sequence of positive
integers admits a finite colouring of the integers with no monochromatic difference in the sequence. -/
example (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (ε : ℝ) (hε : 0 < ε)
    (hlac : ∀ k, (1 + ε) * (n k : ℝ) ≤ n (k + 1)) :
    ∃ (r : ℕ) (c : ℤ → Fin r), ∀ a b : ℤ, c a = c b → ∀ k, a - b ≠ (n k : ℤ) :=
  Erdos894.erdos_894 n ⟨hpos, ε, hε, hlac⟩

/-- The colouring of the natural numbers asked for on the problem page. -/
example (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (ε : ℝ) (hε : 0 < ε)
    (hlac : ∀ k, (1 + ε) * (n k : ℝ) ≤ n (k + 1)) :
    ∃ (r : ℕ) (c : ℕ → Fin r), ∀ a b : ℕ, c a = c b → ∀ k, a ≠ b + n k :=
  Erdos894.erdos_894_nat n ⟨hpos, ε, hε, hlac⟩
