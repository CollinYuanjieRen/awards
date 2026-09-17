import Erdos806SmallBases

open Filter Asymptotics

#print axioms Erdos806.erdos_806
#print axioms Erdos806.erdos_806_eps
#print axioms Erdos806.exists_basis_bound
#print axioms Erdos806.exists_shift
#print axioms Erdos806.card_univSet
#print axioms Erdos806.exists_chunks
#print axioms Erdos806.exists_pow_between

/-- Erdős Problem 806: there is a bound `β n = o(√n)` such that every `A ⊆ {1, …, n}` with
`|A| ≤ √n` is contained in `B + B` for some `B ⊂ ℤ` with `|B| ≤ β n`. -/
example :
    ∃ β : ℕ → ℕ, (fun n : ℕ => (β n : ℝ)) =o[atTop] (fun n : ℕ => Real.sqrt n) ∧
      ∀ n, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ Real.sqrt n →
        ∃ B : Finset ℤ, Erdos806.HasBasis A B ∧ B.card ≤ β n :=
  Erdos806.erdos_806

/-- The explicit `ε`–`N` form: for every `ε > 0` and all large `n`, every such `A` has a basis
of size at most `ε √n`. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n → (A.card : ℝ) ≤ Real.sqrt n →
      ∃ B : Finset ℤ, Erdos806.HasBasis A B ∧ (B.card : ℝ) ≤ ε * Real.sqrt n :=
  Erdos806.erdos_806_eps ε hε

/-- `HasBasis` unfolds to `A ⊆ B + B` elementwise. -/
example (A : Finset ℕ) (B : Finset ℤ) :
    Erdos806.HasBasis A B ↔ ∀ a ∈ A, ∃ b ∈ B, ∃ b' ∈ B, (a : ℤ) = b + b' := Iff.rfl
