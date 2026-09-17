import Erdos772Sidon

open Filter

#print axioms Erdos772.erdos_772
#print axioms Erdos772.erdos_772_closed
#print axioms Erdos772.exists_sidon_subset
#print axioms Erdos772.exists_subset_few_bad
#print axioms Erdos772.card_badTuples_le
#print axioms Erdos772.card_badTuples_repeat_le
#print axioms Erdos772.H_lower
#print axioms Erdos772.tendsto_H_div_sqrt
#print axioms Erdos772.eventually_rpow_lt_H

/-- Erdős Problem 772 (Alon–Erdős): for every `k ≥ 1`, `H_k(n) / n^{1/2} → ∞` and
`H_k(n) > n^{1/2 + c}` for all large `n`, for some `c > 0`. -/
example (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (Erdos772.H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < Erdos772.H k n :=
  Erdos772.erdos_772 k hk

/-- The closed form. -/
example :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ ¬ (Tendsto (fun n : ℕ => (Erdos772.H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ))
      atTop atTop ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < Erdos772.H k n) :=
  Erdos772.erdos_772_closed

/-- The explicit lower bound behind both statements: some `s` with `n² < 6k(s+1)³` has
`s ≤ 2 H_k(n)`, i.e. `H_k(n) ≥ ((n²/6k)^{1/3} − 1)/2`. -/
example (k n : ℕ) (hk : 1 ≤ k) : ∃ s, n ^ 2 < 6 * k * (s + 1) ^ 3 ∧ s ≤ 2 * Erdos772.H k n :=
  Erdos772.H_lower k n hk

/-- The definitions unfold as intended. -/
example (A : Finset ℕ) (m : ℕ) :
    Erdos772.rep A m = ((A ×ˢ A).filter (fun p => p.1 + p.2 = m)).card := rfl
example (k : ℕ) (A : Finset ℕ) : Erdos772.RepBounded k A ↔ ∀ m, Erdos772.rep A m ≤ k := Iff.rfl
example (S : Finset ℕ) : Erdos772.IsSidon S ↔
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  Iff.rfl
example (k n : ℕ) : Erdos772.H k n = sSup {r : ℕ | r ≤ n ∧ ∀ A : Finset ℕ, A.card = n →
    Erdos772.RepBounded k A → ∃ S ⊆ A, Erdos772.IsSidon S ∧ r ≤ S.card} := rfl
