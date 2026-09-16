import Mathlib

/-!
# Erdős Problem 343 (JSP-000285): frozen target statement

Source (erdosproblems.com/343, hashed copy in `ref/erdos343-statement.txt`):
"If `A ⊆ ℕ` is a multiset of integers such that `|A ∩ {1,…,N}| ≫ N` for all `N`
then must `A` be subcomplete?  That is, must `P(A) = {∑_{n∈B} n : B ⊆ A finite}`
contain an infinite arithmetic progression?"  Answered positively by
Szemerédi–Vu (JAMS 2006, Theorem 6.x "Folkman's conjecture"): there is an
absolute constant `C` such that every non-decreasing sequence of positive
integers with `A(n) ≥ C n` for all sufficiently large `n` is subcomplete.

Encoding (identical to plby/lean-proofs `Erdos343` so the two faces are
comparable): a multiset is an occurrence-indexed function `A : ℕ → ℕ`; distinct
indices are distinct occurrences even when the values agree.
-/

namespace Erdos343

open Filter

/-- Finite subset sums of an infinite multiset represented by indexed occurrences. -/
def SubsetSums (A : ℕ → ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, n = ∑ i ∈ s, A i}

/-- A set contains an infinite arithmetic progression with positive difference. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ S

/-- The occurrence-indexed multiset `A` is subcomplete. -/
def IsSubcomplete (A : ℕ → ℕ) : Prop :=
  ContainsInfiniteAP (SubsetSums A)

/-- At least `C * N` occurrences have value at most `N` (for every `N`). -/
def HasLinearCountingLowerBound (C : ℕ) (A : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ s : Finset ℕ, C * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N

/-- The published (Szemerédi–Vu) hypothesis: at least `C * N` occurrences have
value at most `N` for all sufficiently large `N`. -/
def HasEventualLinearCountingLowerBound (C : ℕ) (A : ℕ → ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ s : Finset ℕ, C * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N

end Erdos343
