import Mathlib

/-!
# JSP-000680 / Erdős #824 — a finite lower bound on `h(x)`

`h x` counts the integers `1 ≤ a < b < x` with `(a,b) = 1` and `σ(a) = σ(b)`, where
`σ = ArithmeticFunction.sigma 1` is the sum-of-divisors function
(`ArithmeticFunction.sigma 1 n = ∑ d ∈ n.divisors, d`).

We formalize the finite fact `h 18 ≥ 3`, witnessed by the three coprime, equal-`σ` pairs
`(6, 11)` (`σ = 12`), `(14, 15)` (`σ = 24`) and `(10, 17)` (`σ = 18`).
-/

namespace Erdos824

open ArithmeticFunction

/-- `h x` counts coprime pairs `1 ≤ a < b < x` with equal sum of divisors. -/
def h (x : ℕ) : ℕ :=
  (((Finset.Ico 1 x) ×ˢ (Finset.Ico 1 x)).filter
    (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      ArithmeticFunction.sigma 1 p.1 = ArithmeticFunction.sigma 1 p.2)).card

theorem three_le_h_eighteen : 3 ≤ h 18 := by
  have hsub : ({(6, 11), (14, 15), (10, 17)} : Finset (ℕ × ℕ)) ⊆
      (((Finset.Ico 1 18) ×ˢ (Finset.Ico 1 18)).filter
        (fun p => p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          ArithmeticFunction.sigma 1 p.1 = ArithmeticFunction.sigma 1 p.2)) := by
    decide
  calc 3 = ({(6, 11), (14, 15), (10, 17)} : Finset (ℕ × ℕ)).card := by decide
    _ ≤ h 18 := Finset.card_le_card hsub

end Erdos824

#print axioms Erdos824.three_le_h_eighteen
