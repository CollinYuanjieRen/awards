import MerLeanExperiment.External.Erdos441
import Mathlib.Data.Nat.Sqrt

namespace Erdos441

private theorem g_mono {m n : ℕ} (hmn : m ≤ n) : g m ≤ g n := by
  obtain ⟨A, hA, hcard⟩ := exists_extremal m
  rw [← hcard]
  apply card_le_g
  constructor
  · intro x hx
    have hx' := Finset.mem_Icc.mp (hA.1 hx)
    exact Finset.mem_Icc.mpr ⟨hx'.1, hx'.2.trans hmn⟩
  · intro x hx y hy
    exact (hA.2 x hx y hy).trans hmn

/-- A uniform squared lower bound for the Erdős extremal function. -/
theorem lower_squared_bound (N : ℕ) :
    9 * N ≤ 8 * (g N + 11) ^ 2 := by
  let s := Nat.sqrt (N / 72)
  have hs_upper : N / 72 < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' (N / 72)
  have hmod : N % 72 < 72 := Nat.mod_lt N (by norm_num)
  have hdivmod := Nat.div_add_mod N 72
  have hN_upper : N < 72 * (s + 1) ^ 2 := by omega
  by_cases hs0 : s = 0
  · simp [hs0] at hN_upper
    have hg11 : 11 ≤ g N + 11 := by omega
    have hsq := Nat.pow_le_pow_left hg11 2
    calc
      9 * N ≤ 9 * 71 := by omega
      _ ≤ 8 * 11 ^ 2 := by norm_num
      _ ≤ 8 * (g N + 11) ^ 2 := Nat.mul_le_mul_left 8 hsq
  · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
    let t := s - 1
    have hs_lower : s ^ 2 ≤ N / 72 := by
      simpa [s] using Nat.sqrt_le' (N / 72)
    have h72 : 72 * s ^ 2 ≤ N := by
      calc
        72 * s ^ 2 ≤ 72 * (N / 72) := Nat.mul_le_mul_left 72 hs_lower
        _ = (N / 72) * 72 := by ring
        _ ≤ N := Nat.div_mul_le_self N 72
    have hfamily : familyN t ≤ N := by
      have hform : familyN t = 2 * (6 * s - 2) ^ 2 := by
        simp [familyN, familyK, t]
        omega
      rw [hform]
      calc
        2 * (6 * s - 2) ^ 2 ≤ 2 * (6 * s) ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)
        _ = 72 * s ^ 2 := by ring
        _ ≤ N := h72
    have hfamily_g : g (familyN t) ≤ g N := g_mono hfamily
    have hsource := nine_mul_add_seven_le_g_familyN t
    have hlow : 9 * t + 7 ≤ g N := hsource.trans hfamily_g
    have hg : 9 * (s + 1) ≤ g N + 11 := by
      dsimp [t] at hlow
      omega
    have hsq := Nat.pow_le_pow_left hg 2
    have hscaled : 9 * N < 8 * (9 * (s + 1)) ^ 2 := by
      calc
        9 * N < 9 * (72 * (s + 1) ^ 2) :=
          Nat.mul_lt_mul_of_pos_left hN_upper (by norm_num)
        _ = 8 * (9 * (s + 1)) ^ 2 := by ring
    exact (Nat.le_of_lt hscaled).trans (Nat.mul_le_mul_left 8 hsq)

end Erdos441
