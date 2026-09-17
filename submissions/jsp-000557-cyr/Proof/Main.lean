import Mathlib

/-!
# Erdős problem #685 — the trivial lower bound on `ω(C(n,k))` (scoped component)

The problem page for Erdős problem #685 asks whether, for `ε > 0` and `n` large,
the number of distinct prime divisors of `C(n,k)` is `(1+o(1)) k Σ_{k<p<n} 1/p`
for all `n^ε < k ≤ n^{1-ε}`.  Alongside that open question the page records a
remark it calls *trivial*: the number of prime factors is `> log C(n,k) / log n`.

This package proves that trivial bound, in its correct non-strict form.  Every
prime power `p ^ v_p(C(n,k))` dividing `C(n,k)` is at most `n`
(Kummer/Legendre; Mathlib's `Nat.pow_factorization_choose_le`, restated here as
`pow_factorization_choose_le'`), so writing `C(n,k)` as the product of its prime
powers gives the multiplicative form `C(n,k) ≤ n ^ ω(C(n,k))`
(`choose_le_pow_card_primeFactors`), valid for every `n` and `k`.  Taking
logarithms gives `log C(n,k) ≤ ω(C(n,k)) · log n` (`log_choose_le_card_mul_log`,
again for every `n`, with Lean's convention `Real.log 0 = 0`), and dividing by
`log n > 0` gives the page's form `ω(C(n,k)) ≥ log C(n,k) / log n` for every
`n ≥ 2` (`log_choose_div_log_le_card`).  Here `ω(m)` is `m.primeFactors.card`.

The inequality on the page is written strictly; it is not strict in degenerate
cases, and `strict_fails_two_one` records the equality instance at `n = 2`,
`k = 1`, where `C(2,1) = 2` and `log 2 / log 2 = 1 = ω(2)`.

Not claimed here: the strict inequality written on the page (which fails at `n = 2`, `k = 1`), the asymptotic-equality remark for `k > n^{1-o(1)}`, and the question of Erdős problem #685 whether `ω(C(n,k)) = (1+o(1)) k Σ_{k<p<n} 1/p`.

All objects are Mathlib's (`Nat.choose`, `Nat.primeFactors`, `Nat.factorization`,
`Real.log`); this module introduces no definitions of its own.
-/

namespace Erdos685

/-- Every prime power dividing `C(n,k)` is at most `n` (Kummer/Legendre).
Restatement of Mathlib's `Nat.pow_factorization_choose_le` with explicit binders. -/
theorem pow_factorization_choose_le' (n k p : ℕ) (hn : 0 < n) :
    p ^ (n.choose k).factorization p ≤ n :=
  Nat.pow_factorization_choose_le hn

/-- The multiplicative form of the trivial bound: `C(n,k) ≤ n ^ ω(C(n,k))`. -/
theorem choose_le_pow_card_primeFactors (n k : ℕ) :
    n.choose k ≤ n ^ (n.choose k).primeFactors.card := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rcases k with _ | k
    · simp
    · simp
  · rcases Nat.eq_zero_or_pos (n.choose k) with h0 | h0
    · rw [h0]
      exact Nat.zero_le _
    · have hne : n.choose k ≠ 0 := h0.ne'
      calc n.choose k
          = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p :=
            Nat.prod_primeFactors_pow_factorization hne
        _ ≤ n ^ (n.choose k).primeFactors.card := by
            refine Finset.prod_le_pow_card _ _ _ ?_
            intro p _
            exact pow_factorization_choose_le' n k p hn

/-- The logarithmic form: `log C(n,k) ≤ ω(C(n,k)) · log n`, for every `n` and `k`
(with Lean's convention `Real.log 0 = 0`). -/
theorem log_choose_le_card_mul_log (n k : ℕ) :
    Real.log (n.choose k) ≤ ((n.choose k).primeFactors.card : ℝ) * Real.log n := by
  rcases Nat.eq_zero_or_pos (n.choose k) with h0 | h0
  · rw [h0]
    rw [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)
  · have hpos : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast h0
    have hle : ((n.choose k : ℕ) : ℝ) ≤ ((n : ℝ) ^ (n.choose k).primeFactors.card) := by
      exact_mod_cast choose_le_pow_card_primeFactors n k
    calc Real.log (n.choose k)
        ≤ Real.log ((n : ℝ) ^ (n.choose k).primeFactors.card) := Real.log_le_log hpos hle
      _ = ((n.choose k).primeFactors.card : ℝ) * Real.log n := Real.log_pow _ _

/-- The page's form of the trivial bound: `ω(C(n,k)) ≥ log C(n,k) / log n` for `n ≥ 2`. -/
theorem log_choose_div_log_le_card (n k : ℕ) (hn : 2 ≤ n) :
    Real.log (n.choose k) / Real.log n ≤ ((n.choose k).primeFactors.card : ℝ) := by
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
  rw [div_le_iff₀ (Real.log_pos h1)]
  exact log_choose_le_card_mul_log n k

/-- The inequality on the page is not strict: at `n = 2`, `k = 1` both sides are `1`. -/
theorem strict_fails_two_one :
    Real.log (Nat.choose 2 1) / Real.log 2 = ((Nat.choose 2 1).primeFactors.card : ℝ) := by
  have hc : Nat.choose 2 1 = 2 := by decide
  have hpf : (Nat.choose 2 1).primeFactors = {2} := by
    rw [hc]
    exact Nat.Prime.primeFactors Nat.prime_two
  rw [hpf, hc]
  norm_num


end Erdos685
