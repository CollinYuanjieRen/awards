import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
An elementary implication between the two divisor questions in the canonical
Erdős 387 file. This file does not prove the negative answer to either question.
The finite initial segment is patched with the genuine divisor 1.
-/

namespace Erdos387Proof

open Filter

theorem exists_uniform_of_eventually_half
    (h : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc ((1 / 2 : ℝ) * n) n ∧ d ∣ n.choose k) :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let c : ℝ := min (1 / 2) (1 / ((N : ℝ) + 1))
  have hNp : 0 < (N : ℝ) + 1 := by positivity
  refine ⟨c, lt_min (by norm_num) (one_div_pos.mpr hNp), ?_⟩
  intro n k hk hkn
  by_cases hn : N ≤ n
  · obtain ⟨d, hd, hdiv⟩ := hN n hn k hk hkn
    refine ⟨d, ⟨?_, hd.2⟩, hdiv⟩
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Nat.cast_nonneg n)) hd.1
  · have hnN : (n : ℝ) < (N : ℝ) + 1 := by exact_mod_cast (by omega : n < N + 1)
    have hsmall : (1 / ((N : ℝ) + 1)) * n < 1 := by
      rw [one_div_mul_eq_div]
      exact (div_lt_one hNp).mpr hnN
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    refine ⟨1, ⟨?_, by simpa using hn1⟩, one_dvd _⟩
    simpa only [Nat.cast_one] using
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (Nat.cast_nonneg n)) hsmall

theorem guy_property_implies_uniform
    (h : ∀ c : ℝ, c < 1 → ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k) :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k :=
  exists_uniform_of_eventually_half (h (1 / 2) (by norm_num))

end Erdos387Proof
