import Erdos124GcdNecessary

open Filter Erdos124
open scoped Pointwise

#print axioms erdos_124_gcd_eq_one_of_eventually
#print axioms erdos_124_gcd_closed

/-- Erdős #124: `gcd(d₁,…,d_r) = 1` is necessary in the second question. -/
example (k : ℕ) (hk : k ≠ 0) (D : Finset ℕ) (hD : ∀ d ∈ D, 3 ≤ d)
    (h : ∀ᶠ n in atTop, n ∈ ∑ d ∈ D, sumsOfDistinctPowers d k) : D.gcd id = 1 :=
  erdos_124_gcd_eq_one_of_eventually k hk D hD h

/-- The definition is the formal-conjectures one. -/
example (d k : ℕ) : sumsOfDistinctPowers d k =
    {x | ∃ s : Finset ℕ, (∀ i ∈ s, k ≤ i) ∧ ∑ i ∈ s, d ^ i = x} := rfl
