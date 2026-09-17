import Erdos381Lower.Defs

/-!
# Erdős #381 (JSP-000315): frozen root faces (sorry-stated interface; proved elsewhere)

Catalog target: determine the growth of `Q(x)`, the number of highly composite numbers `≤ x`.
Erdős (1944): `Q(x) ≥ (log x)^{1+c}`; Nicolas (1971): `Q(x) ≤ (log x)^{C}` (the latter is
`Erdos381.NicolasPolynomialUpperBound`, proved in plby/lean-proofs).
-/

namespace Erdos381Lower

open Erdos381 Filter

/-- Erdős 1944, the gap theorem: for every sufficiently large highly composite `n` the next
highly composite number is within a factor `1 + (log n)^{-c}`. -/
theorem erdos381_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, HighlyComposite n →
      ∃ n' : ℕ, HighlyComposite n' ∧ n < n' ∧
        (n' : ℝ) < n + n * Real.log n ^ (-c) := by
  sorry

/-- Erdős 1944: `Q(N) ≥ (log N)^{1+c}` for all large `N`. -/
theorem erdos381_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Real.log N ^ (1 + c) ≤ (Q N : ℝ) := by
  sorry

/-- The two-sided growth statement: Erdős's lower bound together with Nicolas's polynomial upper
bound (`Erdos381.NicolasPolynomialUpperBound`, plby/lean-proofs). -/
theorem erdos381_two_sided :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Real.log N ^ (1 + c) ≤ (Q N : ℝ)) ∧
      NicolasPolynomialUpperBound := by
  sorry

end Erdos381Lower
