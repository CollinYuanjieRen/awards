import Erdos732Designs.Lower.Profiles
import Erdos732Designs.Lower.Asymptotics
import Erdos732Designs.Encoding

/-!
# Erdős Problem 732 — the lower bound (Alon)

For every `n ≥ 256` there is a prime `p` with `p * p ≤ n` and `Nat.sqrt n < 2 * p`
(`exists_prime_sq_le`).  The profiles `Fin (p - 2) → Fin (p + 1)` give
`(p + 1) ^ (p - 2)` pairwise distinct block-compatible multisets for `n`
(`exists_many_blockCompatible`), and `(p + 1) ^ (p - 2) ≥ exp ((1/32) √n log n)`
(`exp_le_pow`).  Together with the finiteness statement from the counting encoding this gives
the lower bound with `c = 1/32` and `N = 256`.
-/

namespace Erdos732Lower

open Erdos732Upper

/-- **Erdős Problem 732, lower bound (Alon).** -/
theorem erdos_732_lower : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    {S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.Finite ∧
      Real.exp (c * Real.sqrt n * Real.log n) ≤
        ({S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.ncard : ℝ) := by
  refine ⟨1 / 32, by norm_num, 256, fun n hn => ?_⟩
  obtain ⟨hfin, -⟩ := Erdos732Upper.blockCompatible_finite_and_ncard_le n (Nat.sqrt (2 * n) + 1)
    (Nat.lt_succ_sqrt (2 * n))
  refine ⟨hfin, ?_⟩
  obtain ⟨p, hp, hpn, hlow⟩ := exists_prime_sq_le n (by omega)
  have := Fact.mk hp
  obtain ⟨f, hfinj, hfc⟩ := exists_many_blockCompatible p n hpn
  have hrange : (Set.range f).ncard = (p + 1) ^ (p - 2) := by
    rw [Set.ncard_range_of_injective hfinj, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
  have hcard : (p + 1) ^ (p - 2) ≤ {S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.ncard := by
    rw [← hrange]
    exact Set.ncard_le_ncard (Set.range_subset_iff.2 hfc) hfin
  calc Real.exp ((1 / 32 : ℝ) * Real.sqrt n * Real.log n)
      ≤ (((p + 1) ^ (p - 2) : ℕ) : ℝ) := exp_le_pow n p hn hp hpn hlow
    _ ≤ ({S : Multiset ℕ | Erdos732Upper.BlockCompatible n S}.ncard : ℝ) := by
        exact_mod_cast hcard

end Erdos732Lower
