import Proof.Pell

/-!
# Erdős Problem 1147: the phase identity at the Pell scales

For `N = N_j`, `P = P_j` and a split `N = n₁ + n₂`, one has
`√2 n₂² = ((N - 2 n₁) P) / 2 - ρ_j / 2 + n₁ η_j + √2 n₁²`.
Since `(N - 2 n₁) P` is odd, `√2 n₂² ≡ 1/2 + t + √2 n₁² (mod 1)` with
`t = n₁ η_j - ρ_j / 2`, `|t| ≤ ρ_j / 2 < 9 / 100`.

Two consequences:
* (both summands close to integers is impossible) if `‖√2 n₁²‖ ≤ ε₀` and `‖√2 n₂²‖ ≤ ε₀` with
  `ε₀ ≤ 1/5`, then `‖√2 n₂² - √2 n₁²‖ ≤ 2/5`, while it equals `‖1/2 + t‖ ≥ 1/2 - 9/100`;
* (a fixed first summand) for fixed `n₁ ≥ 1`, `‖√2 (N_j - n₁)²‖` stays bounded away from `0`
  for large `j`, because its phase tends to `θ = 1/2 - 1/(8√2) + √2 n₁²`, which is not an
  integer as `√2` is irrational.
-/

open Filter

namespace Erdos1147

/-- The exact phase identity. -/
theorem phase_identity (j n₁ : ℕ) (h : n₁ ≤ pN j) :
    Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2 =
      (((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) / 2 - rho j / 2 + n₁ * eta j
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2 := by
  have hP : (pP j : ℝ) = eta j + 2 * Real.sqrt 2 * (pN j : ℝ) := by
    rw [eta]; ring
  have hr : rho j = eta j * (pN j : ℝ) := rfl
  rw [Nat.cast_sub h, hr]
  push_cast
  linear_combination (2 * (n₁ : ℝ) - (pN j : ℝ)) / 2 * hP

/-- `(N_j - 2 n₁) P_j` is odd. -/
theorem odd_phase_int (j n₁ : ℕ) : Odd (((pN j : ℤ) - 2 * n₁) * (pP j : ℤ)) := by
  obtain ⟨k, hk⟩ := pN_odd j
  obtain ⟨l, hl⟩ := pP_odd j
  refine Odd.mul ⟨(k : ℤ) - n₁, ?_⟩ ⟨(l : ℤ), ?_⟩
  · rw [hk]; push_cast; ring
  · rw [hl]; push_cast; ring

/-- `nd (√2 n₂²) = nd (1/2 + t + √2 n₁²)` with `t = n₁ η_j - ρ_j / 2`. -/
theorem nd_phase (j n₁ : ℕ) (h : n₁ ≤ pN j) :
    nd (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) =
      nd (1 / 2 + (n₁ * eta j - rho j / 2) + Real.sqrt 2 * (n₁ : ℝ) ^ 2) := by
  rw [phase_identity j n₁ h]
  have hsplit : (((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) / 2 - rho j / 2 + n₁ * eta j
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2
      = ((((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) : ℝ) / 2
        + ((n₁ : ℝ) * eta j - rho j / 2 + Real.sqrt 2 * (n₁ : ℝ) ^ 2) := by
    ring
  rw [hsplit, nd_odd_div_two_add _ (odd_phase_int j n₁)]
  congr 1
  ring

/-- `|n₁ η_j - ρ_j / 2| ≤ ρ_j / 2` for `n₁ ≤ N_j`. -/
theorem abs_shift_le (j n₁ : ℕ) (h : n₁ ≤ pN j) : |n₁ * eta j - rho j / 2| ≤ rho j / 2 := by
  have hr : rho j = eta j * (pN j : ℝ) := rfl
  have h0 : (0 : ℝ) ≤ (n₁ : ℝ) * eta j := mul_nonneg (Nat.cast_nonneg _) (eta_pos j).le
  have h1 : (n₁ : ℝ) * eta j ≤ rho j := by
    rw [hr, mul_comm (eta j) ((pN j : ℝ))]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) (eta_pos j).le
  rw [abs_le]
  constructor <;> linarith

/-- Both summands of a split of `N_j` cannot both have `‖√2 n²‖ ≤ ε₀` when `ε₀ ≤ 1/5`. -/
theorem not_both_close (j n₁ : ℕ) (h : n₁ ≤ pN j) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 5)
    (h₁ : nd (Real.sqrt 2 * (n₁ : ℝ) ^ 2) ≤ ε₀)
    (h₂ : nd (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) ≤ ε₀) : False := by
  have hsub := nd_sub_le (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) (Real.sqrt 2 * (n₁ : ℝ) ^ 2)
  have hshift := abs_shift_le j n₁ h
  have hrho := rho_lt_num j
  have ht : |(n₁ : ℝ) * eta j - rho j / 2| ≤ 1 / 2 := by linarith
  have key : Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2 - Real.sqrt 2 * (n₁ : ℝ) ^ 2
      = ((((pN j : ℤ) - 2 * n₁) * (pP j : ℤ) : ℤ) : ℝ) / 2
        + ((n₁ : ℝ) * eta j - rho j / 2) := by
    rw [phase_identity j n₁ h]; ring
  rw [key, nd_odd_div_two_add _ (odd_phase_int j n₁)] at hsub
  have hlow := half_sub_abs_le_nd_half_add _ ht
  linarith

/-- The limiting phase for a fixed first summand `n₁`. -/
noncomputable def theta (n₁ : ℕ) : ℝ := 1 / 2 - 1 / (8 * Real.sqrt 2) + Real.sqrt 2 * (n₁ : ℝ) ^ 2

/-- `θ n₁` is never an integer (for `n₁ ≥ 1`, and in fact for all `n₁`, since `16 n₁² ≠ 1`). -/
theorem nd_theta_pos (n₁ : ℕ) : 0 < nd (theta n₁) := by
  rcases (nd_nonneg (theta n₁)).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨m, hm⟩ := (nd_eq_zero_iff (theta n₁)).1 h.symm
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hspos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h8 : 1 / (8 * Real.sqrt 2) = Real.sqrt 2 / 16 := by
    rw [eq_div_iff (by norm_num : (16 : ℝ) ≠ 0), div_mul_eq_mul_div,
      div_eq_iff (by positivity : (8 : ℝ) * Real.sqrt 2 ≠ 0)]
    linear_combination -8 * hs
  rw [theta, h8] at hm
  have hkey : Real.sqrt 2 * (16 * (n₁ : ℝ) ^ 2 - 1) = 16 * (m : ℝ) - 8 := by
    linear_combination 16 * hm
  have hd : (16 * (n₁ : ℝ) ^ 2 - 1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · rw [h0]; norm_num
    · have h1 : (1 : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast h0
      have : (0 : ℝ) < 16 * (n₁ : ℝ) ^ 2 - 1 := by nlinarith
      exact ne_of_gt this
  refine irrational_sqrt_two ⟨(16 * (m : ℚ) - 8) / (16 * (n₁ : ℚ) ^ 2 - 1), ?_⟩
  push_cast
  rw [div_eq_iff hd]
  linarith [hkey]

/-- For a fixed first summand, the second summand's phase is eventually bounded away from the
integers: `nd (√2 (N_j - n₁)²) ≥ nd (θ n₁) / 2` once `N_j` is large. -/
theorem nd_second_summand_ge (n₁ : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      nd (theta n₁) / 2 ≤ nd (Real.sqrt 2 * ((pN j - n₁ : ℕ) : ℝ) ^ 2) := by
  have hc : 0 < nd (theta n₁) := nd_theta_pos n₁
  refine ⟨n₁ + ⌈2 * ((n₁ : ℝ) + 1) / nd (theta n₁)⌉₊ + 1, fun j hj => ?_⟩
  have hjN : j + 1 ≤ pN j := succ_le_pN j
  have hle : n₁ ≤ pN j := by omega
  have hKle : ⌈2 * ((n₁ : ℝ) + 1) / nd (theta n₁)⌉₊ ≤ pN j := by omega
  have hn0 : (0 : ℝ) ≤ (n₁ : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (pN j : ℝ) := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ (pN j : ℝ) := by exact_mod_cast pN_pos j
  have hNpos : (0 : ℝ) < (pN j : ℝ) := by linarith
  have hNr : 2 * ((n₁ : ℝ) + 1) / nd (theta n₁) ≤ (pN j : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hKle)
  have hNc : 2 * ((n₁ : ℝ) + 1) ≤ (pN j : ℝ) * nd (theta n₁) := (div_le_iff₀ hc).1 hNr
  rw [nd_phase j n₁ hle]
  have h8 : 1 / (8 * Real.sqrt 2) = 1 / (4 * Real.sqrt 2) / 2 := by
    rw [div_div]; ring_nf
  have hdiff : theta n₁ - (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2)
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2)
      = -((n₁ : ℝ) * eta j) - (1 / (4 * Real.sqrt 2) - rho j) / 2 := by
    rw [theta, h8]; ring
  have hA0 : (0 : ℝ) ≤ (n₁ : ℝ) * eta j := mul_nonneg hn0 (eta_pos j).le
  have hB := abs_rho_sub_le j
  have hB0 : (0 : ℝ) ≤ |1 / (4 * Real.sqrt 2) - rho j| := abs_nonneg _
  have e1 : |theta n₁ - (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2)
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2)|
      ≤ (n₁ : ℝ) * eta j + |1 / (4 * Real.sqrt 2) - rho j| / 2 := by
    rw [hdiff, abs_le]
    refine ⟨?_, ?_⟩
    · linarith [le_abs_self (1 / (4 * Real.sqrt 2) - rho j)]
    · linarith [neg_abs_le (1 / (4 * Real.sqrt 2) - rho j)]
  have hBN : |1 / (4 * Real.sqrt 2) - rho j| * (32 * (pN j : ℝ) ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity)).1 hB
  have e4 : |1 / (4 * Real.sqrt 2) - rho j| * (pN j : ℝ) ≤ 1 := by
    nlinarith [mul_nonneg hB0 (show (0 : ℝ) ≤ 32 * (pN j : ℝ) ^ 2 - (pN j : ℝ) by nlinarith)]
  have e2 : (n₁ : ℝ) * eta j * (pN j : ℝ) = (n₁ : ℝ) * rho j := by
    rw [rho]; ring
  have e3 : (n₁ : ℝ) * rho j ≤ (n₁ : ℝ) := by
    have h9 : rho j ≤ 1 := by linarith [rho_lt_num j]
    nlinarith
  have hmul : |theta n₁ - (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2)
        + Real.sqrt 2 * (n₁ : ℝ) ^ 2)| * (pN j : ℝ) ≤ (n₁ : ℝ) + 1 := by
    calc _ ≤ ((n₁ : ℝ) * eta j + |1 / (4 * Real.sqrt 2) - rho j| / 2) * (pN j : ℝ) :=
          mul_le_mul_of_nonneg_right e1 hN0
      _ = (n₁ : ℝ) * eta j * (pN j : ℝ)
            + |1 / (4 * Real.sqrt 2) - rho j| * (pN j : ℝ) / 2 := by ring
      _ ≤ (n₁ : ℝ) + 1 := by rw [e2]; linarith
  have key := (le_div_iff₀ hNpos).2 hmul
  have hfin : ((n₁ : ℝ) + 1) / (pN j : ℝ) ≤ nd (theta n₁) / 2 := by
    rw [div_le_iff₀ hNpos]; linarith
  have hlip := nd_le_nd_add_abs_sub (theta n₁)
    (1 / 2 + ((n₁ : ℝ) * eta j - rho j / 2) + Real.sqrt 2 * (n₁ : ℝ) ^ 2)
  linarith

end Erdos1147
