import Erdos439Power.PowerGrowth

open Filter
open scoped Topology
open Erdos439

namespace Erdos439Power

/-- Dividing the raw major-arc estimate by its positive normalization gives
the three scalar error terms used in the final argument. -/
lemma normalized_major_error_bound (S T g q Q e u : ℝ)
    (hT : 0 < T) (hg : 0 ≤ g) (hq : 0 ≤ q) (hQ : 0 < Q)
    (huq : q * u ≤ 1 / Q)
    (hS : S ≤ e * T + 2 * q * (2 * g + (2 * Real.pi * u) * g * T)) :
    T⁻¹ * S ≤ e + 4 * q * g / T + 4 * Real.pi * g / Q := by
  have hqug : q * u * g ≤ g / Q := by
    have := mul_le_mul_of_nonneg_right huq hg
    field_simp at this ⊢
    nlinarith
  have hraw : S ≤ e * T + 4 * q * g + 4 * Real.pi * (q * u * g) * T := by
    nlinarith [Real.pi_pos]
  calc
    T⁻¹ * S ≤ T⁻¹ *
        (e * T + 4 * q * g + 4 * Real.pi * (q * u * g) * T) := by
      exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hT.le)
    _ ≤ T⁻¹ * (e * T + 4 * q * g + 4 * Real.pi * (g / Q) * T) := by
      gcongr
    _ = e + 4 * q * g / T + 4 * Real.pi * g / Q := by
      field_simp

/-- The two normalized geometric errors on a major arc have an explicit
`M⁻³` bound. -/
lemma major_parameter_bound (k L C M q : ℕ) (hk : 1 ≤ k)
    (hM : 2 ≤ M) (hq : q ≤ C * M) :
    let N := M ^ 4
    let Q := M ^ (4 * k - 1)
    let g := normalizedPowerGap k L N
    let T : ℝ := normalizedPower k L N
    let K : ℝ := normalizedPower k L 1
    4 * q * g / T + 4 * Real.pi * g / Q ≤
      (4 * (2 : ℝ) ^ k * ((C : ℝ) + Real.pi * K)) / (M : ℝ) ^ 3 := by
  dsimp only
  let N := M ^ 4
  let g := normalizedPowerGap k L N
  let T : ℝ := normalizedPower k L N
  let K : ℝ := normalizedPower k L 1
  have hN : 1 ≤ N := by
    dsimp [N]
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 4 (by omega))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hTr : (0 : ℝ) < T := by
    dsimp [T]
    exact_mod_cast lt_of_lt_of_le (show 0 < N by omega) (normalizedPower_index_le k L N)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hNg := mul_normalizedPowerGap_le k L N hk hN
  have hgrowth := normalizedPowerGap_le_growth k L N hk hN
  have hg : (0 : ℝ) ≤ g := (normalizedPowerGap_pos k L N).le
  have hqreal : (q : ℝ) ≤ C * M := by exact_mod_cast hq
  have hfirst : 4 * (q : ℝ) * g / T ≤
      4 * (2 : ℝ) ^ k * C / (M : ℝ) ^ 3 := by
    apply (div_le_iff₀ hTr).2
    have hCM : (0 : ℝ) ≤ C * M := by positivity
    have hqg : (q : ℝ) * g ≤ (C : ℝ) * M * g := by gcongr
    have hNM : (N : ℝ) = (M : ℝ) ^ 4 := by norm_num [N]
    rw [hNM] at hNg
    field_simp
    nlinarith
  have hpowid : N ^ (k - 1) * M ^ 3 = M ^ (4 * k - 1) := by
    dsimp [N]
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hsecond : 4 * Real.pi * g / (M : ℝ) ^ (4 * k - 1) ≤
      4 * (2 : ℝ) ^ k * (Real.pi * K) / (M : ℝ) ^ 3 := by
    have hQpos : (0 : ℝ) < (M : ℝ) ^ (4 * k - 1) := pow_pos hMr _
    apply (div_le_iff₀ hQpos).2
    have hpowidr : (N : ℝ) ^ (k - 1) * (M : ℝ) ^ 3 =
        (M : ℝ) ^ (4 * k - 1) := by exact_mod_cast hpowid
    have hcancel :
        (4 * (2 : ℝ) ^ k * (Real.pi * K) / (M : ℝ) ^ 3) *
            (M : ℝ) ^ (4 * k - 1) =
          4 * Real.pi * ((2 : ℝ) ^ k * K * (N : ℝ) ^ (k - 1)) := by
      rw [← hpowidr]
      field_simp
    rw [hcancel]
    exact mul_le_mul_of_nonneg_left hgrowth (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
  push_cast
  calc
    4 * (q : ℝ) * g / T + 4 * Real.pi * g / (M : ℝ) ^ (4 * k - 1) ≤
        4 * (2 : ℝ) ^ k * C / (M : ℝ) ^ 3 +
          4 * (2 : ℝ) ^ k * (Real.pi * K) / (M : ℝ) ^ 3 :=
      add_le_add hfirst hsecond
    _ = (4 * (2 : ℝ) ^ k * ((C : ℝ) + Real.pi * K)) / (M : ℝ) ^ 3 := by ring

/-- For fixed construction parameters, the explicit major-arc scalar tends
to zero. -/
theorem tendsto_major_parameter_scalar (k L C : ℕ) :
    Tendsto (fun M : ℕ =>
      (4 * (2 : ℝ) ^ k * ((C : ℝ) + Real.pi * (normalizedPower k L 1 : ℝ))) /
        (M : ℝ) ^ 3) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop)

theorem eventually_major_parameter_scalar_le (k L C : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      (4 * (2 : ℝ) ^ k * ((C : ℝ) + Real.pi * (normalizedPower k L 1 : ℝ))) /
        (M : ℝ) ^ 3 ≤ ε :=
  (tendsto_major_parameter_scalar k L C).eventually_le_const hε

end Erdos439Power
