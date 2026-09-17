import Erdos894Colouring.Definitions

/-! Splitting a lacunary sequence into finitely many subsequences of ratio at least `4`. -/

namespace Erdos894

/-- A lacunary sequence has some `r ≥ 1` such that every subsequence `i ↦ n (j + r * i)` grows by
a factor at least `4`. -/
theorem exists_split_of_isLacunary (n : ℕ → ℕ) (hn : IsLacunary n) :
    ∃ r : ℕ, 0 < r ∧ ∀ j i : ℕ, 4 * n (j + r * i) ≤ n (j + r * (i + 1)) := by
  obtain ⟨-, ε, hε, hstep⟩ := hn
  -- Iterating the one-step estimate `(1 + ε) * n k ≤ n (k + 1)`.
  have key : ∀ k t : ℕ, (1 + ε) ^ t * (n k : ℝ) ≤ (n (k + t) : ℝ) := by
    intro k t
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 : (0 : ℝ) ≤ 1 + ε := by linarith
      calc (1 + ε) ^ (t + 1) * (n k : ℝ) = (1 + ε) * ((1 + ε) ^ t * (n k : ℝ)) := by ring
        _ ≤ (1 + ε) * (n (k + t) : ℝ) := mul_le_mul_of_nonneg_left ih h1
        _ ≤ (n (k + t + 1) : ℝ) := hstep _
        _ = (n (k + (t + 1)) : ℝ) := by rw [Nat.add_assoc]
  -- Choose `r` large enough that `(1 + ε) ^ r ≥ 4`, via Bernoulli's inequality.
  set N := ⌈3 / ε⌉₊ with hN
  refine ⟨N + 1, Nat.succ_pos _, ?_⟩
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  have h3 : 3 ≤ (N : ℝ) * ε := by
    have h := Nat.le_ceil (3 / ε)
    rw [hN, ← div_le_iff₀ hε]
    exact h
  have h4 : (4 : ℝ) ≤ (1 + ε) ^ (N + 1) := by
    have hb : 1 + ((N + 1 : ℕ) : ℝ) * ε ≤ (1 + ε) ^ (N + 1) :=
      one_add_mul_le_pow (by linarith) (N + 1)
    have hexp : ((N + 1 : ℕ) : ℝ) * ε = (N : ℝ) * ε + ε := by rw [hcast]; ring
    linarith
  intro j i
  have hk := key (j + (N + 1) * i) (N + 1)
  have hidx : j + (N + 1) * i + (N + 1) = j + (N + 1) * (i + 1) := by ring
  rw [hidx] at hk
  have hnn : (0 : ℝ) ≤ (n (j + (N + 1) * i) : ℝ) := Nat.cast_nonneg _
  have hfin : (4 : ℝ) * (n (j + (N + 1) * i) : ℝ) ≤ (n (j + (N + 1) * (i + 1)) : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right h4 hnn) hk
  exact_mod_cast hfin

end Erdos894
