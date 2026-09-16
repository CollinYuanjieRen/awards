import Proof.Defs

/-!
# Erdős Problem 1147: the Pell sequence for `√2`

The pairs `(x_j, y_j)` with `x_j + y_j √2 = (3 + 2√2)^(2j+1)` satisfy `x_j² - 2 y_j² = 1`, `x_j`
is odd and `y_j ≡ 2 (mod 4)`.  We set `N_j := y_j / 2` (an odd positive integer, tending to
infinity) and `P_j := x_j`, so that `P_j² = 8 N_j² + 1`.  The defect `η_j := P_j - 2√2 N_j` is
positive and tiny, and `ρ_j := η_j N_j` tends to `1 / (4√2)`.
-/

open Filter

namespace Erdos1147

/-- `pell j = (x_j, y_j)` with `x_j + y_j √2 = (3 + 2√2)^(2j+1)`; each step multiplies by
`(3 + 2√2)² = 17 + 12√2`. -/
def pell : ℕ → ℕ × ℕ
  | 0 => (3, 2)
  | j + 1 => (17 * (pell j).1 + 24 * (pell j).2, 12 * (pell j).1 + 17 * (pell j).2)

/-- `P_j = x_j`. -/
def pP (j : ℕ) : ℕ := (pell j).1

/-- `y_j`. -/
def pY (j : ℕ) : ℕ := (pell j).2

/-- `N_j = y_j / 2`. -/
def pN (j : ℕ) : ℕ := pY j / 2

theorem pP_succ (j : ℕ) : pP (j + 1) = 17 * pP j + 24 * pY j := rfl

theorem pY_succ (j : ℕ) : pY (j + 1) = 12 * pP j + 17 * pY j := rfl

theorem pell_identity (j : ℕ) : pP j ^ 2 = 2 * pY j ^ 2 + 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pP_succ, pY_succ]
    zify at ih ⊢
    linear_combination ih

theorem pP_odd (j : ℕ) : Odd (pP j) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.odd_iff] at ih ⊢
    rw [pP_succ]
    omega

theorem pY_mod_four (j : ℕ) : pY j % 4 = 2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pY_succ]
    omega

theorem two_mul_pN (j : ℕ) : 2 * pN j = pY j := by
  have h := pY_mod_four j
  unfold pN
  omega

theorem pN_odd (j : ℕ) : Odd (pN j) := by
  have h := pY_mod_four j
  rw [Nat.odd_iff]
  unfold pN
  omega

theorem pN_pos (j : ℕ) : 0 < pN j := by
  have h := pY_mod_four j
  unfold pN
  omega

/-- `N_{j+1} ≥ 17 N_j`, hence `N_j ≥ j + 1`. -/
theorem succ_le_pN (j : ℕ) : j + 1 ≤ pN j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h1 := two_mul_pN (j + 1)
    have h2 := two_mul_pN j
    have h3 := pY_succ j
    have h4 := Nat.odd_iff.1 (pP_odd j)
    omega

theorem pN_strictMono : StrictMono pN := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  have h1 := two_mul_pN (j + 1)
  have h2 := two_mul_pN j
  have h3 := pY_succ j
  have h4 := Nat.odd_iff.1 (pP_odd j)
  omega

theorem tendsto_pN : Tendsto (fun j => (pN j : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast Nat.le_of_succ_le (succ_le_pN j)

/-- `P_j² = 8 N_j² + 1` in `ℝ`. -/
theorem pP_sq_real (j : ℕ) : (pP j : ℝ) ^ 2 = 8 * (pN j : ℝ) ^ 2 + 1 := by
  have h : (pP j : ℝ) ^ 2 = 2 * (pY j : ℝ) ^ 2 + 1 := by exact_mod_cast pell_identity j
  have h2 : (pY j : ℝ) = 2 * (pN j : ℝ) := by exact_mod_cast (two_mul_pN j).symm
  rw [h2] at h
  linarith

/-- The defect `η_j = P_j - 2√2 N_j`. -/
noncomputable def eta (j : ℕ) : ℝ := (pP j : ℝ) - 2 * Real.sqrt 2 * pN j

theorem eta_mul (j : ℕ) : eta j * ((pP j : ℝ) + 2 * Real.sqrt 2 * pN j) = 1 := by
  have hdef : eta j = (pP j : ℝ) - 2 * Real.sqrt 2 * (pN j : ℝ) := rfl
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hdef]
  linear_combination pP_sq_real j - 4 * (pN j : ℝ) ^ 2 * hsq

theorem eta_pos (j : ℕ) : 0 < eta j := by
  have hP : 0 < pP j := by
    have h := Nat.odd_iff.1 (pP_odd j)
    omega
  have hP' : (0 : ℝ) < (pP j : ℝ) := by exact_mod_cast hP
  have hden : (0 : ℝ) < (pP j : ℝ) + 2 * Real.sqrt 2 * pN j := by
    have h : (0 : ℝ) ≤ 2 * Real.sqrt 2 * (pN j : ℝ) := by positivity
    linarith
  nlinarith [eta_mul j, hden]

/-- `η_j ≤ 1 / (4√2 N_j)`. -/
theorem eta_le (j : ℕ) : eta j ≤ 1 / (4 * Real.sqrt 2 * pN j) := by
  have hNpos : (0 : ℝ) < (pN j : ℝ) := by exact_mod_cast pN_pos j
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hc : (0 : ℝ) < 4 * Real.sqrt 2 * (pN j : ℝ) := mul_pos (by linarith) hNpos
  rw [le_div_iff₀ hc]
  have hkey : eta j * (4 * Real.sqrt 2 * (pN j : ℝ)) + eta j * eta j
      = eta j * ((pP j : ℝ) + 2 * Real.sqrt 2 * pN j) := by
    unfold eta
    ring
  linarith [eta_mul j, hkey, mul_self_nonneg (eta j)]

theorem eta_le_one (j : ℕ) : eta j ≤ 1 := by
  have h := eta_le j
  have hN1 : (1 : ℝ) ≤ (pN j : ℝ) := by
    have h1 : 1 ≤ pN j := pN_pos j
    exact_mod_cast h1
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hc : (1 : ℝ) ≤ 4 * Real.sqrt 2 * (pN j : ℝ) := by nlinarith
  have hle : 1 / (4 * Real.sqrt 2 * (pN j : ℝ)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  linarith

/-- `ρ_j = η_j N_j`. -/
noncomputable def rho (j : ℕ) : ℝ := eta j * pN j

theorem rho_pos (j : ℕ) : 0 < rho j := by
  have hN : (0 : ℝ) < (pN j : ℝ) := by exact_mod_cast pN_pos j
  unfold rho
  exact mul_pos (eta_pos j) hN

/-- The exact gap to the limit: `1 / (4√2) - ρ_j = η_j² / (4√2)`. -/
private theorem one_div_sub_rho (j : ℕ) :
    1 / (4 * Real.sqrt 2) - rho j = eta j ^ 2 / (4 * Real.sqrt 2) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h4 : (4 : ℝ) * Real.sqrt 2 ≠ 0 := by positivity
  have hdef : eta j = (pP j : ℝ) - 2 * Real.sqrt 2 * (pN j : ℝ) := rfl
  have hrho : rho j = eta j * (pN j : ℝ) := rfl
  have hkey : 1 - 4 * Real.sqrt 2 * rho j = eta j ^ 2 := by
    rw [hrho]
    linear_combination (-1 : ℝ) * eta_mul j - eta j * hdef
  field_simp
  linarith [hkey]

/-- `ρ_j < 1 / (4√2)`. -/
theorem rho_lt (j : ℕ) : rho j < 1 / (4 * Real.sqrt 2) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h := one_div_sub_rho j
  have hpos : 0 < eta j ^ 2 / (4 * Real.sqrt 2) :=
    div_pos (pow_pos (eta_pos j) 2) (by linarith)
  linarith

/-- Numerical form: `ρ_j < 9 / 50` (note `1 / (4√2) ≈ 0.1768`). -/
theorem rho_lt_num (j : ℕ) : rho j < 9 / 50 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h25 : (25 : ℝ) / 18 < Real.sqrt 2 := by nlinarith
  have h : 1 / (4 * Real.sqrt 2) < 9 / 50 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith [rho_lt j]

/-- `|1 / (4√2) - ρ_j| ≤ 1 / (32 N_j²)`. -/
theorem abs_rho_sub_le (j : ℕ) : |1 / (4 * Real.sqrt 2) - rho j| ≤ 1 / (32 * (pN j : ℝ) ^ 2) := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hN1 : (1 : ℝ) ≤ (pN j : ℝ) := by
    have h1 : 1 ≤ pN j := pN_pos j
    exact_mod_cast h1
  have hid := one_div_sub_rho j
  have hnn : 0 ≤ 1 / (4 * Real.sqrt 2) - rho j := by
    rw [hid]
    positivity
  rw [abs_of_nonneg hnn, hid]
  have hc : (0 : ℝ) < 4 * Real.sqrt 2 * (pN j : ℝ) := by nlinarith
  have h1 : eta j * (4 * Real.sqrt 2 * (pN j : ℝ)) ≤ 1 := by
    rw [← le_div_iff₀ hc]
    exact eta_le j
  have h0 : 0 ≤ eta j * (4 * Real.sqrt 2 * (pN j : ℝ)) := mul_nonneg (eta_pos j).le hc.le
  have hsqle : (eta j * (4 * Real.sqrt 2 * (pN j : ℝ))) ^ 2 ≤ 1 := by nlinarith
  have hexp : (eta j * (4 * Real.sqrt 2 * (pN j : ℝ))) ^ 2
      = eta j ^ 2 * (32 * (pN j : ℝ) ^ 2) := by
    linear_combination (16 * eta j ^ 2 * (pN j : ℝ) ^ 2) * hsq
  rw [hexp] at hsqle
  rw [div_le_div_iff₀ (by linarith) (by nlinarith)]
  linarith

end Erdos1147
