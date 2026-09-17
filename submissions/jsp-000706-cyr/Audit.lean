import Erdos853GapsEven

open OeisA92243

#print axioms primeGap_even
#print axioms primeGap_ne_odd
#print axioms primeGap_even_closed

/-- Erdős #853: every prime gap other than the first is even, so restricting `r(x)` to even `t`
is necessary. -/
example (n : ℕ) (hn : n ≠ 1) : Even (primeGap n) := primeGap_even n hn
example (t : ℕ) (ht : Odd t) (ht1 : 1 < t) : ¬ ∃ n, primeGap n = t := primeGap_ne_odd t ht ht1

/-- The definition is the formal-conjectures one. -/
example (n : ℕ) : primeGap n = Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1) := rfl
