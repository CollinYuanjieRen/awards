import Erdos732Designs.Design

/-!
# Asymptotics for the lower bound

Two elementary estimates feeding the lower bound for Erdős Problem 732.

`exists_prime_sq_le` produces, for `n ≥ 16`, a prime `p` with `p * p ≤ n` and `Nat.sqrt n < 2 * p`:
Bertrand's postulate applied to `k = Nat.sqrt n / 2` gives a prime `p` with `k < p ≤ 2 * k`, and
`2 * k ≤ Nat.sqrt n` while `Nat.sqrt n < 2 * k + 2 ≤ 2 * p`.

`exp_le_pow` turns such a prime into the growth estimate
`exp ((1/32) * √n * log n) ≤ (p + 1) ^ (p - 2)`, via `√n / 4 ≤ p - 2` and
`(1/8) * log n ≤ log (p + 1)`.
-/

namespace Erdos732Lower

/-- A prime `p` with `p² ≤ n` and `√n < 2p` (Bertrand applied to `Nat.sqrt n / 2`). -/
theorem exists_prime_sq_le (n : ℕ) (hn : 16 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p * p ≤ n ∧ Nat.sqrt n < 2 * p := by
  have hs : 4 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  obtain ⟨p, hp, hkp, hp2k⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt n / 2) (by omega)
  refine ⟨p, hp, ?_, by omega⟩
  have hple : p ≤ Nat.sqrt n := by omega
  calc p * p ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hple hple
    _ ≤ n := Nat.sqrt_le n

theorem exp_le_pow (n p : ℕ) (hn : 256 ≤ n) (hp : p.Prime) (hpn : p * p ≤ n)
    (hlow : Nat.sqrt n < 2 * p) :
    Real.exp ((1 / 32 : ℝ) * Real.sqrt n * Real.log n) ≤ ((p + 1 : ℕ) ^ (p - 2) : ℕ) := by
  have hp2 : 2 ≤ p := hp.two_le
  -- `n < (2 * p) ^ 2`: the only arithmetic input about `p`.
  have hn4 : n < 2 * p * (2 * p) :=
    lt_of_lt_of_le (Nat.lt_succ_sqrt n) (Nat.mul_le_mul (by omega) (by omega))
  have hnR : (256 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `0 < n` from `p * p ≤ n` (the hypothesis `hpn`); the bound `256 ≤ n` is used separately.
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (Nat.mul_pos hp.pos hp.pos) hpn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hpR0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hn4R : (n : ℝ) < (2 * (p : ℝ)) ^ 2 := by
    have h : (n : ℝ) < ((2 * p * (2 * p) : ℕ) : ℝ) := by exact_mod_cast hn4
    push_cast at h
    nlinarith [h]
  -- `16 ≤ √n < 2 * p`, hence `9 ≤ p`.
  have hsq16 : (16 : ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) hn0.le).2 (by linarith)
  have hsqlt : Real.sqrt n < 2 * (p : ℝ) := (Real.sqrt_lt' (by linarith)).2 hn4R
  have hp9 : 9 ≤ p := by
    have h8 : (8 : ℝ) < (p : ℝ) := by linarith
    have : 8 < p := by exact_mod_cast h8
    omega
  have hp9R : (9 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp9
  -- Step 1: `√n / 4 ≤ p - 2`.
  have hA : Real.sqrt n / 4 ≤ (p : ℝ) - 2 := by linarith
  -- Step 2: `(1/8) * log n ≤ log (p + 1)`.
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog2 : 8 * Real.log 2 ≤ Real.log n := by
    have h256 : Real.log 256 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow] at h256
    push_cast at h256
    linarith
  have hup : Real.log n ≤ 2 * Real.log 2 + 2 * Real.log ((p : ℝ) + 1) := by
    have hle : (n : ℝ) ≤ (2 * ((p : ℝ) + 1)) ^ 2 := by nlinarith
    have h := Real.log_le_log hn0 hle
    rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h
    push_cast at h
    linarith
  have hB : 1 / 8 * Real.log n ≤ Real.log ((p : ℝ) + 1) := by linarith
  -- Step 3: combine.
  have key : (1 / 32 : ℝ) * Real.sqrt n * Real.log n ≤ ((p : ℝ) - 2) * Real.log ((p : ℝ) + 1) := by
    have hrw : (1 / 32 : ℝ) * Real.sqrt n * Real.log n
        = Real.sqrt n / 4 * (1 / 8 * Real.log n) := by ring
    rw [hrw]
    exact mul_le_mul hA hB (by linarith) (by linarith)
  have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    have := Nat.cast_sub (R := ℝ) (show 2 ≤ p by omega)
    push_cast at this ⊢
    linarith [this]
  calc Real.exp ((1 / 32 : ℝ) * Real.sqrt n * Real.log n)
      ≤ Real.exp (((p : ℝ) - 2) * Real.log ((p : ℝ) + 1)) := Real.exp_le_exp.2 key
    _ = ((p : ℝ) + 1) ^ (p - 2) := by
        rw [← hcast, ← Real.log_pow, Real.exp_log (by positivity)]
    _ = (((p + 1 : ℕ) ^ (p - 2) : ℕ) : ℝ) := by push_cast; ring

end Erdos732Lower
