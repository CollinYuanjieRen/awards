import Erdos732Designs.Main
import Erdos732Designs.Lower

/-!
# Erdős Problem 732 — the counting question, both bounds

`Erdos732.erdos_732` combines the upper bound `Erdos732Upper.erdos_732_upper` (Erdős; proof
printed in Alon's note, §3) with the lower bound `Erdos732Lower.erdos_732_lower` (Alon, Theorem 2.3):
there are absolute constants `c, C > 0` such that for all large `n` the number of block-compatible
size multisets for `n` lies between `exp (c √n log n)` and `exp (C √n log n)`. In particular the
answer to the page's question "is there some `c > 0` such that for all large `n` there are at least
`exp (c n^{1/2} log n)` block-compatible sequences?" is YES, and the bound is sharp up to the constant.
-/

namespace Erdos732

/-- **Erdős Problem 732 (counting question), both bounds.** -/
theorem erdos_732 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    {S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.Finite ∧
      Real.exp (c * Real.sqrt n * Real.log n) ≤
        ({S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.ncard : ℝ) ∧
      ({S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.ncard : ℝ) ≤
        Real.exp (C * Real.sqrt n * Real.log n) := by
  obtain ⟨C, hC, N₁, hup⟩ := Erdos732Upper.erdos_732_upper
  obtain ⟨c, hc, N₂, hlow⟩ := Erdos732Lower.erdos_732_lower
  refine ⟨c, C, hc, hC, max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨hfin, hle⟩ := hup n (le_trans (le_max_left _ _) hn)
  obtain ⟨-, hge⟩ := hlow n (le_trans (le_max_right _ _) hn)
  exact ⟨hfin, hge, hle⟩

end Erdos732
