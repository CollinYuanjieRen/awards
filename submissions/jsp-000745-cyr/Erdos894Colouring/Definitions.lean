import Mathlib

/-!
# Erdős Problem 894: colourings avoiding lacunary differences

Erdős (1987, reported by Katznelson) asked: if `n₁ < n₂ < ⋯` is a lacunary sequence of positive
integers (`n (k+1) ≥ (1 + ε) n k` for some `ε > 0`), must there be a finite colouring of the
integers with no monochromatic solution to `a - b = n k`? The answer is yes (Katznelson 2001,
following the Diophantine result of Pollington / de Mathan; quantitative form by Peres–Schlag).

This file fixes the statement. The proof is the classical rotation argument: split the sequence
into finitely many subsequences of ratio at least `4`, choose for each a real `θ` whose multiples
`θ · n k` all have fractional part in `[1/4, 3/4]`, and colour an integer by the cells of the
fractional parts `θ_j · m`.
-/

namespace Erdos894

/-- A sequence of positive integers is lacunary if consecutive terms grow by a fixed factor
`1 + ε > 1`. -/
def IsLacunary (n : ℕ → ℕ) : Prop :=
  (∀ k, 0 < n k) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ k, (1 + ε) * (n k : ℝ) ≤ n (k + 1)

/-- A colouring of the integers with finitely many colours in which no two integers of the same
colour differ by a term of `n`. -/
def HasAvoidingColouring (n : ℕ → ℕ) : Prop :=
  ∃ (r : ℕ) (c : ℤ → Fin r), ∀ a b : ℤ, c a = c b → ∀ k, a - b ≠ (n k : ℤ)

end Erdos894
