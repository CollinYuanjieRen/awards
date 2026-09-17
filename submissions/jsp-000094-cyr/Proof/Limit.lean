import Proof.Sharp
import Proof.Lower

/-!
# Erdős problem #77 — the Erdős bounds `√2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 4`

Combining the counting lower bound `R(k)² > 2^k` of `MerLeanExperiment.Lower` with the
Erdős–Szekeres upper bound `R(k) ≤ C(2k-2, k-1)` of `MerLeanExperiment.Sharp` we obtain the
two termwise estimates

* `Erdos77.sqrt_two_le_R_rpow` : `√2 ≤ R(k)^{1/k}` for `k ≥ 3`;
* `Erdos77.R_rpow_le_four`     : `R(k)^{1/k} ≤ 4` for `k ≥ 1`,

and hence the two bounds recorded on the Erdős problem page,

* `Erdos77.sqrt_two_le_liminf` : `√2 ≤ liminf R(k)^{1/k}`;
* `Erdos77.limsup_le_four`     : `limsup R(k)^{1/k} ≤ 4`.

Not claimed here: the question of Erdős problem #77 itself (the existence and value of
lim R(k)^{1/k}), which is open, and the improved upper bounds 4 − 1/128, 3.7992… and 4 − c.
-/

namespace Erdos77

/-- The Erdős–Szekeres bound in the crude exponential form `R(k) ≤ 4^k`, via
`R(k) ≤ C(2k-2, k-1) ≤ 2^{2k-2} ≤ 2^{2k} = 4^k`. -/
theorem R_le_four_pow (k : ℕ) (hk : 1 ≤ k) : R k ≤ 4 ^ k := by
  have h1 : R k ≤ (2 * k - 2).choose (k - 1) := R_le_choose k hk
  have h2 : (2 * k - 2).choose (k - 1) ≤ 2 ^ (2 * k - 2) := Nat.choose_le_two_pow _ _
  have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h3 : (2 : ℕ) ^ (2 * k - 2) ≤ 4 ^ k := by
    rw [h4]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Termwise lower bound: `R(k)^{1/k} ≥ √2` for `k ≥ 3` (from `R(k)² > 2^k`). -/
theorem sqrt_two_le_R_rpow (k : ℕ) (hk : 3 ≤ k) : Real.sqrt 2 ≤ (R k : ℝ) ^ (1 / (k : ℝ)) := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkpos : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  -- `2^{k/2} ≤ R k`, obtained by comparing squares
  have hR : (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (R k : ℝ) := by
    have hnat : (2 : ℕ) ^ k < R k ^ 2 := two_pow_lt_R_sq k hk
    have hcast : (2 : ℝ) ^ k < (R k : ℝ) ^ 2 := by exact_mod_cast hnat
    have hsq : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ k := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num),
        show (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = (k : ℝ) by push_cast; ring]
      exact Real.rpow_natCast 2 k
    refine (sq_le_sq₀ (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)).mp ?_
    rw [hsq]
    exact hcast.le
  have hstep : (2 : ℝ) ^ (1 / 2 : ℝ) = ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ (1 / (k : ℝ)) := by
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    field_simp
  rw [Real.sqrt_eq_rpow, hstep]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hR hkpos

/-- Termwise upper bound: `R(k)^{1/k} ≤ 4` for `k ≥ 1` (from `R(k) ≤ C(2k−2, k−1) ≤ 4^k`). -/
theorem R_rpow_le_four (k : ℕ) (hk : 1 ≤ k) : (R k : ℝ) ^ (1 / (k : ℝ)) ≤ 4 := by
  have hk0 : k ≠ 0 := by omega
  have hle : (R k : ℝ) ≤ (4 : ℝ) ^ k := by exact_mod_cast R_le_four_pow k hk
  have h4 : ((4 : ℝ) ^ k) ^ (1 / (k : ℝ)) = 4 := by
    rw [one_div, Real.pow_rpow_inv_natCast (by norm_num) hk0]
  calc (R k : ℝ) ^ (1 / (k : ℝ))
      ≤ ((4 : ℝ) ^ k) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by positivity)
    _ = 4 := h4

/-- The sequence `R(k)^{1/k}` is bounded above (by `4`), hence `liminf` is well behaved. -/
theorem isBoundedUnder_le_R_rpow :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) :=
  ⟨4, Filter.eventually_map.mpr
    (Filter.eventually_atTop.mpr ⟨1, fun k hk => R_rpow_le_four k hk⟩)⟩

/-- The sequence `R(k)^{1/k}` is bounded below (by `0`), hence `limsup` is well behaved. -/
theorem isBoundedUnder_ge_R_rpow :
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) :=
  ⟨0, Filter.eventually_map.mpr
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)⟩

/-- Erdős: `√2 ≤ liminf R(k)^{1/k}`. -/
theorem sqrt_two_le_liminf :
    Real.sqrt 2 ≤ Filter.liminf (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop :=
  Filter.le_liminf_of_le isBoundedUnder_le_R_rpow.isCoboundedUnder_ge
    (Filter.eventually_atTop.mpr ⟨3, fun k hk => sqrt_two_le_R_rpow k hk⟩)

/-- Erdős: `limsup R(k)^{1/k} ≤ 4`. -/
theorem limsup_le_four :
    Filter.limsup (fun k : ℕ => (R k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop ≤ 4 :=
  Filter.limsup_le_of_le isBoundedUnder_ge_R_rpow.isCoboundedUnder_le
    (Filter.eventually_atTop.mpr ⟨1, fun k hk => R_rpow_le_four k hk⟩)

end Erdos77
