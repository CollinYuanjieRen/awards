import Erdos1183Lattices.Chain
import Erdos1183Lattices.Counting

/-!
# Erdős Problem 1183 — phase 1 result

Combining the chain lower bound (`le_f`) with the double-counting upper bound (`f_le`) gives the
two-sided estimate `(n + 2) / 2 ≤ f n ≤ (n + 1) ^ 2`.
-/

namespace Erdos1183

/-- Phase-1 bounds for Erdős problem 1183: `⌈(n+1)/2⌉ ≤ f n ≤ (n + 1) ^ 2`. -/
theorem erdos_1183_closed :
    (∀ n : ℕ, (n + 2) / 2 ≤ f n) ∧ (∀ n : ℕ, f n ≤ (n + 1) ^ 2) :=
  ⟨fun n => le_f n, fun n => f_le n⟩

end Erdos1183
