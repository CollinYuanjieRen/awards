/- leanprover/lean4:v4.34.0-rc1  mathlib 1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d -/
/-
Comparator challenge module for the JSP-000399 submission (Erdős Problem 494, Selfridge–Straus
criteria).  It imports only Mathlib and restates the two definitions (verbatim from
google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/494.lean`) and the two target
statements with `sorry`, for mechanical comparison against the solution module `Proof.Main`.
-/

import Mathlib

namespace Erdos494

noncomputable def sumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => s.sum id

def Erdos494Unique (k : ℕ) (card : ℕ) :=
  ∀ A B : Finset ℂ, A.card = card → B.card = card → sumMultiset A k = sumMultiset B k → A = B

/-- Selfridge–Straus: `A` is determined by `A_k` if a prime greater than `k` divides `|A|`. -/
theorem card_divisible_by_prime_gt_k :
    ∀ (k card p : ℕ), p.Prime → k ∈ Set.Ioo 0 p → p ∣ card → Erdos494Unique k card := by
  sorry

/-- Selfridge–Straus: for `k = 2`, `A` is determined by `A_2` if `|A|` is not a power of two. -/
theorem k_eq_2_card_not_pow_two :
    ∀ card : ℕ, (∀ l : ℕ, card ≠ 2 ^ l) → Erdos494Unique 2 card := by
  sorry

end Erdos494
