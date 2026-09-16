import Mathlib

/-! Comparator-style challenge module (Mathlib-only definitions, targets with `sorry`; not
imported by the build) for JSP-000773 / Erdős #931, the two page-stated examples. -/

namespace Challenge931

/-- `∏_{1 ≤ i ≤ k} (n + i)` -/
def consProd (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)

def SamePrimeFactors (n₁ k₁ n₂ k₂ : ℕ) : Prop :=
  (consProd n₁ k₁).primeFactors = (consProd n₂ k₂).primeFactors

/-- Tijdeman: 19·20·21·22 and 54·55·56·57 -/
theorem tijdeman : SamePrimeFactors 18 4 53 4 ∧ 3 ≤ 4 ∧ 18 + 4 ≤ 53 := by
  sorry

/-- AlphaProof: 10! and 14·15·16, with n₂ = 13 ≤ 2(n₁ + k₁) = 20 -/
theorem alphaproof : SamePrimeFactors 0 10 13 3 ∧ 3 ≤ 3 ∧ 3 ≤ 10 ∧ 0 + 10 ≤ 13 ∧ 13 ≤ 2 * (0 + 10) := by
  sorry

theorem erdos_guess_false :
    ¬ ∀ n₁ k₁ n₂ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ → n₁ + k₁ ≤ n₂ → SamePrimeFactors n₁ k₁ n₂ k₂ →
      2 * (n₁ + k₁) < n₂ := by
  sorry

end Challenge931
