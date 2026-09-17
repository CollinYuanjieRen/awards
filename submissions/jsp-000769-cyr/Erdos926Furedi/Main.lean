import Erdos926Furedi.Count

/-! # Erdős Problem 926 -/

namespace Erdos926

open SimpleGraph Finset Filter Asymptotics

/-- The extremal number of `H_k` with explicit constants (Füredi 1991). -/
theorem extremalNumber_Hk_le (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    (extremalNumber n (Hk k) : ℝ) ≤
      (k : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) + k * n := by
  classical
  have key : ∀ ⦃G : SimpleGraph (Fin n)⦄ [DecidableRel G.Adj], (Hk k).Free G →
      (#G.edgeFinset : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) + k * n := by
    intro G _ hfree
    have h := card_edgeFinset_le_of_free k hk G hfree
    rwa [Fintype.card_fin] at h
  have hnonneg : (0 : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) + k * n := by
    positivity
  have h2 := (extremalNumber_le_iff_of_nonneg (V := Fin n) (Hk k) hnonneg).mpr key
  rwa [Fintype.card_fin] at h2

/-- Erdős Problem 926: for every `k ≥ 4`, `ex(n; H_k) = O(n^{3/2})`. -/
theorem erdos_926 (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ => (extremalNumber n (Hk k) : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ) := by
  refine IsBigO.of_bound (2 * (k : ℝ) ^ (3 / 2 : ℝ)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := extremalNumber_Hk_le k (by omega) n
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkpow : (k : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) := by
    calc (k : ℝ) = (k : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hnpow : (n : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hkpos : (0 : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hnpos : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hextr : (0 : ℝ) ≤ (extremalNumber n (Hk k) : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hextr, abs_of_nonneg hnpos]
  have hmul : (k : ℝ) * n ≤ (k : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_le_mul hkpow hnpow (by positivity) hkpos
  linarith

/-- Closed form of `erdos_926`: there is no `k ≥ 4` for which `ex(n; H_k)` fails to be
`O(n^{3/2})`. -/
theorem erdos_926_closed :
    ¬ ∃ k : ℕ, 4 ≤ k ∧
      ¬ ((fun n : ℕ => (extremalNumber n (Hk k) : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) :=
  fun ⟨k, hk, h⟩ => h (erdos_926 k hk)

end Erdos926
