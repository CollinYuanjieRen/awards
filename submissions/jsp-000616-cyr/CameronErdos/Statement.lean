import Mathlib

/-!
# JSP-000616 / Erdős #748 — the Cameron–Erdős conjecture (frozen target)

`f(n)` counts the sum-free subsets of `{1, …, n}`, where a set `A` is sum-free if
there are no `a, b, c ∈ A` with `a + b = c` (`a = b` allowed; equivalently
`(A + A) ∩ A = ∅`).  The conjecture proper (Cameron–Erdős 1990; proved by Green 2004
and Sapozhenko 2003) is `f(n) = O(2^{n/2})`.

The root is stated squared to stay in `ℕ`: `f(n)^2 ≤ C · 2^n` for all `n` is
equivalent to `f(n) ≤ √C · 2^{n/2}`.
-/

namespace CameronErdos

/-- `A` is sum-free: no `a, b ∈ A` (equality allowed) with `a + b ∈ A`. -/
def IsSumFree (A : Finset ℕ) : Prop := ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A

instance (A : Finset ℕ) : Decidable (IsSumFree A) := by
  unfold IsSumFree; infer_instance

/-- The number of sum-free subsets of `{1, …, n}`. -/
def sumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter IsSumFree).card

/-- Sanity: the first values agree with OEIS A007865 (1, 2, 3, 6, 9, 16, 24). -/
example : (List.range 7).map sumFreeCount = [1, 2, 3, 6, 9, 16, 24] := by decide

/-- The Cameron–Erdős conjecture proper: `f(n) = O(2^{n/2})`. -/
def CameronErdosStatement : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, sumFreeCount n ^ 2 ≤ C * 2 ^ n

/- Real-valued reading (derived later in `Assembly.lean`, not part of the frozen root):
`∃ C > 0, ∀ n, (sumFreeCount n : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2)`. -/

end CameronErdos
