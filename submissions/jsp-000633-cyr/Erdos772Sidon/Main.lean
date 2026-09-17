import Erdos772Sidon.Bounds

/-! # Erdős Problem 772 -/

namespace Erdos772

open Filter

/-- Erdős Problem 772 (Alon–Erdős): for every `k ≥ 1`, `H_k(n) / n^{1/2} → ∞`, and
`H_k(n) > n^{1/2 + c}` for all large `n` with some `c > 0`. -/
theorem erdos_772 (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < H k n :=
  ⟨tendsto_H_div_sqrt k hk, 1 / 12, by norm_num, eventually_rpow_lt_H k hk⟩

/-- The closed form: there is no `k ≥ 1` for which the two statements fail. -/
theorem erdos_772_closed :
    ¬ ∃ k : ℕ, 1 ≤ k ∧ ¬ (Tendsto (fun n : ℕ => (H k n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < H k n) := by
  rintro ⟨k, hk, h⟩
  exact h (erdos_772 k hk)

end Erdos772
