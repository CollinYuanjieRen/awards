import Erdos770PrimeIff

open Set ENat Filter Erdos770

#print axioms erdos_770_h_eq_add_one_succ
#print axioms Erdos770.Nat.Prime.h_eq_add_one

/-- Erdős #770: `h n = n + 1 ↔ (n + 1).Prime` for `n > 2`, in the formal-conjectures shape. -/
example {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime := Erdos770.Nat.Prime.h_eq_add_one hn

/-- The definition is the formal-conjectures one. -/
example (n : ℕ) : h n = sInf {m | 2 < m ∧
    ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1} := rfl
