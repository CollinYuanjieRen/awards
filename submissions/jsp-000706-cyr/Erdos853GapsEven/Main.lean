import Mathlib

/-!
# Erdős Problem #853: every prime gap after the first is even

Let `d_n = p_{n+1} − p_n` be the prime gaps and let `r(x)` be the smallest even `t` such that
`d_n = t` has no solution with `n ≤ x`; Erdős asked whether `r(x) → ∞` and whether
`r(x)/log x → ∞` (OPEN; not addressed here).  The problem page records: "In [Er85c] Erdős omits
the condition that `t` be even, but this is clearly necessary."  This file proves that remark:
with the formal-conjectures definition `primeGap` (from `FormalConjectures/OEIS/92243.lean`,
`primeGap n = nth Prime n − nth Prime (n − 1)`, so `primeGap 1 = 3 − 2 = 1` is the only odd
gap), every gap `primeGap n` with `n ≠ 1` is even, and hence no odd `t > 1` is ever a prime gap
(so without "even" the function `r` would be constantly `3`).  The questions about `r(x)` are not
claimed.

Proof.  `nth Prime 0 = 2`; for `n ≥ 2` both `nth Prime n` and `nth Prime (n − 1)` are primes
larger than `2` (by strict monotonicity of `nth` on the infinite set of primes), hence odd, and
the difference of two odd numbers is even; `primeGap 0 = 2 − 2 = 0` is even.
-/

namespace OeisA92243

/-- The `n`-th prime gap: `primeGap n = p_{n+1} - p_n` for `n ≥ 1`, where `p_k = Nat.nth Nat.Prime (k - 1)`
is the `k`-th prime (so `Nat.nth Nat.Prime 0 = 2`). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

end OeisA92243

open OeisA92243

/-- Every prime after the first one is odd: for `k ≥ 1` the `k`-th prime `Nat.nth Nat.Prime k`
exceeds `Nat.nth Nat.Prime 0 = 2`, hence is an odd prime. -/
theorem nth_prime_odd_of_two_le {k : ℕ} (hk : 1 ≤ k) : Odd (Nat.nth Nat.Prime k) := by
  have h2 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime k :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
  rw [Nat.nth_prime_zero_eq_two] at h2
  exact (Nat.prime_nth_prime k).odd_of_ne_two (by omega)

/-- **Erdős #853, the page's remark**: every prime gap other than `primeGap 1 = 1` is even. -/
theorem primeGap_even (n : ℕ) (hn : n ≠ 1) : Even (primeGap n) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [primeGap]
  · have ha : Odd (Nat.nth Nat.Prime (n - 1)) := nth_prime_odd_of_two_le (by omega)
    have hb : Odd (Nat.nth Nat.Prime n) := nth_prime_odd_of_two_le (by omega)
    exact Nat.Odd.sub_odd hb ha

/-- Consequently no odd `t > 1` occurs as a prime gap, so the restriction to even `t` in the
definition of `r(x)` is necessary. -/
theorem primeGap_ne_odd (t : ℕ) (ht : Odd t) (ht1 : 1 < t) : ¬ ∃ n, primeGap n = t := by
  rintro ⟨n, hn⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · have h : primeGap 1 = 1 := by
      simp [primeGap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
    omega
  · exact (Nat.not_even_iff_odd.mpr ht) (hn ▸ primeGap_even n hn1)

/-- The same as a closed statement (no binders), used as the graded root. -/
theorem primeGap_even_closed : ¬ ∃ n : ℕ, n ≠ 1 ∧ ¬ Even (primeGap n) := by
  rintro ⟨n, hn, h⟩
  exact h (primeGap_even n hn)
