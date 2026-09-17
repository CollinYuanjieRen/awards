import Mathlib

/-!
# JSP-000731 / Erdős #880 — definitions

Erdős (1998), quoting a problem of Burr and Erdős: an infinite set of integers `A` is an
*asymptotic basis of order `k`* if every sufficiently large integer is the sum of `k` or fewer
elements of `A`.  Let `b₁ < b₂ < ⋯` be the integers that are sums of `k` or fewer *pairwise
distinct* elements of `A`.  Must `b_{i+1} - b_i` be bounded?

This file fixes the objects of the question in our own words.  Nothing here is a theorem.
-/

open Filter

namespace Erdos880

/-- `n` is the sum of at most `k` elements of `A`, repetitions allowed:
there is a multiset of members of `A` of size `≤ k` whose sum is `n`. -/
def IsSumOfAtMost (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ m : Multiset ℕ, (∀ a ∈ m, a ∈ A) ∧ Multiset.card m ≤ k ∧ m.sum = n

/-- `n` is the sum of exactly `k` elements of `A`, repetitions allowed. -/
def IsSumOfExactly (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ m : Multiset ℕ, (∀ a ∈ m, a ∈ A) ∧ Multiset.card m = k ∧ m.sum = n

/-- The integers that are sums of at most `k` pairwise distinct elements of `A`
(the sequence `b₁ < b₂ < ⋯` of the question). -/
def distinctSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ s.card ≤ k ∧ ∑ a ∈ s, a = n}

/-- The integers that are sums of exactly `k` pairwise distinct elements of `A`. -/
def exactDistinctSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, (↑s : Set ℕ) ⊆ A ∧ s.card = k ∧ ∑ a ∈ s, a = n}

/-- Erdős's definition: `A` is an asymptotic basis of order `k` when every sufficiently large
integer is the sum of `k` or fewer elements of `A`. -/
def IsAsymptoticBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ᶠ n in atTop, IsSumOfAtMost A k n

/-- `B` has bounded gaps: for some window length `C`, every sufficiently late window
`[n, n + C]` contains an element of `B`.  For an infinite `B` enumerated as `b₀ < b₁ < ⋯`
this says exactly that `b_{i+1} - b_i` is eventually bounded; see `Enumeration.lean`. -/
def HasBoundedGaps (B : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ᶠ n in atTop, ∃ b ∈ B, n ≤ b ∧ b ≤ n + C

end Erdos880
