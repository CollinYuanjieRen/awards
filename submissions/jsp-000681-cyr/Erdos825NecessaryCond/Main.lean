import Mathlib

/-!
# Erdős Problem #825: the necessary condition `C > 2` (the witness `n = 70`)

Benkoski and Erdős asked for an absolute constant `C > 0` such that every `n` with `σ(n) > C n`
is a sum of distinct proper divisors of `n`; Larsen proved that such a `C` exists (the problem is
PROVED, with a Lean proof by Alexeev in plby/lean-proofs of the formal-conjectures statement
`erdos_825`).  Neither the existence of `C` nor Larsen's theorem is claimed here.  This file
proves the remark recorded on the problem page: "We must have `C > 2` since `σ(70) = 144` but
`70` is not the distinct sum of integers from `{1, 2, 5, 7, 10, 14, 35}`", i.e. the
formal-conjectures statement `erdos_825.variants.necessary_cond` (copied verbatim) together with
the page's witness `seventy_witness`.

Disclosure: that `70` is not a sum of distinct proper divisors is Mathlib's `Nat.weird_seventy`
(`70` is weird); the computations `σ 1 70 = 144`, `properDivisors 70 = {1, 2, 5, 7, 10, 14, 35}`
and the deduction `2 < C` are what this file adds.
-/

open scoped ArithmeticFunction.sigma

namespace Erdos825

/--
Show that if the constant $C > 0$ is such that every integer $n$ with
$\sigma(n) > Cn$ is the distinct sum of proper divisors of $n$, then we
must have $C > 2$.
-/
theorem erdos_825.variants.necessary_cond (C : ℝ) (hC : 0 < C)
    (h : ∀ (n : ℕ) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id) :
    2 < C := by
  by_contra hlt
  push Not at hlt
  -- `hCrange` records the standing hypotheses on `C` (positive, and `≤ 2` by assumption).
  have hCrange : (0 : ℝ) < C ∧ C ≤ 2 := ⟨hC, hlt⟩
  have hs : σ 1 70 = 144 := by rw [ArithmeticFunction.sigma_one_apply]; decide
  -- `σ 70 = 144 > 140 ≥ 70 * C`, so `70` satisfies the hypothesis of `h`.
  obtain ⟨s, hsub, hsum⟩ := h 70 (by rw [hs]; push_cast; linarith [hCrange.1, hCrange.2])
  -- but `70` is weird, i.e. not a sum of distinct proper divisors.
  exact Nat.weird_seventy.2 ⟨by norm_num, s, hsub, hsum.symm⟩

/-- The page's witness: `properDivisors 70 = {1, 2, 5, 7, 10, 14, 35}`, `σ(70) = 144`, and `70`
is not a sum of distinct proper divisors. -/
theorem seventy_witness :
    (70 : ℕ).properDivisors = {1, 2, 5, 7, 10, 14, 35} ∧ σ 1 70 = 144 ∧
      ¬ ∃ s ⊆ (70 : ℕ).properDivisors, 70 = s.sum id := by
  refine ⟨by decide, by rw [ArithmeticFunction.sigma_one_apply]; decide, ?_⟩
  rintro ⟨s, hsub, hsum⟩
  exact Nat.weird_seventy.2 ⟨by norm_num, s, hsub, hsum.symm⟩

end Erdos825

/-- **Erdős #825, the necessary condition `C > 2`, closed form**: no `C` with `0 < C ≤ 2` has
the property that every `n` with `σ(n) > C n` is a sum of distinct proper divisors of `n`. -/
theorem erdos_825_necessary_cond_closed :
    ¬ ∃ C : ℝ, 0 < C ∧ C ≤ 2 ∧
      ∀ (n : ℕ) (_ : σ 1 n > C * n), ∃ s ⊆ n.properDivisors, n = s.sum id := by
  rintro ⟨C, hC, hle, h⟩
  exact absurd (Erdos825.erdos_825.variants.necessary_cond C hC h) (not_lt.mpr hle)
