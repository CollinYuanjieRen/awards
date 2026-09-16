import MerLeanExperiment.ExponentialDivision

open Classical MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos492Real

noncomputable section

/-- A symmetric multiplicative window of logarithmic radius `t`. -/
def multiplicativeWindow (c t : ℝ) : Set ℝ :=
  Icc (c * Real.exp (-t)) (c * Real.exp t)

/-- The arithmetic midpoint of exponential cell `j`. -/
def exponentialMidpoint (q j : ℕ) : ℝ :=
  (exponentialGridPoint q j + exponentialGridPoint q (j + 1)) / 2

/-- Windows around all endpoints of the truncated exponential grid. -/
def endpointExceptional (q : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ j ∈ (Finset.range (q ^ 2 + 1) : Set ℕ),
    multiplicativeWindow (exponentialGridPoint q j) (δ / q)

/-- Windows around all arithmetic cell midpoints. -/
def midpointExceptional (q : ℕ) (δ : ℝ) : Set ℝ :=
  ⋃ j ∈ (Finset.range (q ^ 2) : Set ℕ),
    multiplicativeWindow (exponentialMidpoint q j) (δ / q)

/-- The common exceptional set: the truncated bottom interval together with
all endpoint and midpoint boundary windows. -/
def exponentialExceptionalSet (q : ℕ) (δ : ℝ) : Set ℝ :=
  Icc 0 (Real.exp (-(q : ℝ))) ∪ endpointExceptional q δ ∪ midpointExceptional q δ

theorem measurableSet_exponentialExceptionalSet (q : ℕ) (δ : ℝ) :
    MeasurableSet (exponentialExceptionalSet q δ) := by
  apply MeasurableSet.union
  · exact (measurableSet_Icc.union <|
      Finset.measurableSet_biUnion (Finset.range (q ^ 2 + 1)) fun _ _ => measurableSet_Icc)
  · exact Finset.measurableSet_biUnion (Finset.range (q ^ 2)) fun _ _ => measurableSet_Icc

private theorem exp_window_width_le (q : ℕ) (hq : 0 < q) {δ c : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c) :
    c * Real.exp (δ / q) - c * Real.exp (-(δ / q)) ≤ 4 * c * δ / q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have ht0 : 0 ≤ δ / (q : ℝ) := div_nonneg hδ0 hqr.le
  have ht1 : |δ / (q : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg ht0]
    exact (div_le_one hqr).2 (hδ1.trans (by exact_mod_cast hq))
  have htn1 : |-(δ / (q : ℝ))| ≤ 1 := by simpa using ht1
  have hp := Real.abs_exp_sub_one_le ht1
  have hn := Real.abs_exp_sub_one_le htn1
  have hp' : Real.exp (δ / q) - 1 ≤ 2 * (δ / q) := by
    exact (le_abs_self _).trans (by simpa [abs_of_nonneg ht0] using hp)
  have hn' : 1 - Real.exp (-(δ / q)) ≤ 2 * (δ / q) := by
    have := (neg_le_abs (Real.exp (-(δ / q)) - 1)).trans hn
    simpa [abs_of_nonneg ht0] using this
  calc
    c * Real.exp (δ / q) - c * Real.exp (-(δ / q)) =
        c * ((Real.exp (δ / q) - 1) + (1 - Real.exp (-(δ / q)))) := by ring
    _ ≤ c * (2 * (δ / q) + 2 * (δ / q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hp' hn') hc
    _ = 4 * c * δ / q := by ring

private theorem exponentialGridPoint_sum_le (q : ℕ) (hq : 0 < q) :
    ∑ j ∈ Finset.range (q ^ 2 + 1), exponentialGridPoint q j ≤ 2 * q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let r : ℝ := Real.exp (-(1 / (q : ℝ)))
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (one_div_pos.mpr hqr)
  have hsum : (∑ j ∈ Finset.range (q ^ 2 + 1), exponentialGridPoint q j) =
      ∑ j ∈ Finset.range (q ^ 2 + 1), r ^ j := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ q ^ 2 := by simpa using Finset.mem_range.1 hj
    rw [exponentialGridPoint]
    have heq : q ^ 2 + 1 - 1 - j = q ^ 2 - j := by omega
    rw [heq]
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_sub hjle]
    push_cast
    field_simp
    ring
  rw [hsum]
  have hgeom : (∑ j ∈ Finset.range (q ^ 2 + 1), r ^ j) ≤ (1 - r)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (sub_pos.mpr hr1)]
    have hid := geom_sum_mul r (q ^ 2 + 1)
    have hp : 0 ≤ r ^ (q ^ 2 + 1) := pow_nonneg hr0.le _
    nlinarith
  have hexp : 1 + 1 / (q : ℝ) ≤ Real.exp (1 / q) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / (q : ℝ))
  have hrform : r = (Real.exp (1 / q))⁻¹ := by simp [r, Real.exp_neg]
  have hden : (1 - r)⁻¹ ≤ (q : ℝ) + 1 := by
    rw [hrform]
    have hepos : 0 < Real.exp (1 / (q : ℝ)) := Real.exp_pos _
    have hbase : (q + 1) / q ≤ Real.exp (1 / (q : ℝ)) := by
      calc
        ((q : ℝ) + 1) / q = 1 + 1 / q := by field_simp
        _ ≤ Real.exp (1 / q) := hexp
    have hinv : (Real.exp (1 / (q : ℝ)))⁻¹ ≤ q / (q + 1) := by
      rw [inv_le_comm₀ hepos (by positivity)]
      simpa [div_eq_mul_inv, mul_comm] using hbase
    rw [inv_le_comm₀ (sub_pos.mpr (by simpa [hrform] using hr1)) (by positivity)]
    calc
      ((q : ℝ) + 1)⁻¹ = 1 - q / (q + 1) := by field_simp; ring
      _ ≤ 1 - (Real.exp (1 / q))⁻¹ := sub_le_sub_left hinv 1
  exact hgeom.trans (hden.trans (by exact_mod_cast (show q + 1 ≤ 2 * q by omega)))

private theorem exponentialMidpoint_sum_le (q : ℕ) (hq : 0 < q) :
    ∑ j ∈ Finset.range (q ^ 2), exponentialMidpoint q j ≤ 2 * q := by
  calc
    (∑ j ∈ Finset.range (q ^ 2), exponentialMidpoint q j) ≤
        ∑ j ∈ Finset.range (q ^ 2), exponentialGridPoint q (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [exponentialMidpoint]
      have hmono := exponentialGridPoint_strictMono q hq (Nat.lt_succ_self j)
      linarith
    _ ≤ ∑ j ∈ Finset.range (q ^ 2 + 1), exponentialGridPoint q j := by
      rw [Finset.sum_range_succ']
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    _ ≤ 2 * q := exponentialGridPoint_sum_le q hq

private theorem volume_endpointExceptional_le (q : ℕ) (hq : 0 < q)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    volume (endpointExceptional q δ) ≤ ENNReal.ofReal (8 * δ) := by
  calc
    volume (endpointExceptional q δ) ≤
        ∑ j ∈ Finset.range (q ^ 2 + 1),
          volume (multiplicativeWindow (exponentialGridPoint q j) (δ / q)) := by
      exact measure_biUnion_finset_le _ _
    _ = ∑ j ∈ Finset.range (q ^ 2 + 1), ENNReal.ofReal
          (exponentialGridPoint q j * Real.exp (δ / q) -
            exponentialGridPoint q j * Real.exp (-(δ / q))) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [multiplicativeWindow, Real.volume_Icc]
    _ ≤ ∑ j ∈ Finset.range (q ^ 2 + 1), ENNReal.ofReal
          (4 * exponentialGridPoint q j * δ / q) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal
        (exp_window_width_le q hq hδ0 hδ1 (Real.exp_pos _).le)
    _ = ENNReal.ofReal
          (∑ j ∈ Finset.range (q ^ 2 + 1),
            4 * exponentialGridPoint q j * δ / q) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hδ0)
        (Nat.cast_nonneg _)
    _ ≤ ENNReal.ofReal (8 * δ) := by
      apply ENNReal.ofReal_le_ofReal
      have hsum := exponentialGridPoint_sum_le q hq
      have hqr : (0 : ℝ) < q := by exact_mod_cast hq
      have heq : (∑ j ∈ Finset.range (q ^ 2 + 1),
          4 * exponentialGridPoint q j * δ / q) =
          (4 * δ / q) *
            (∑ j ∈ Finset.range (q ^ 2 + 1), exponentialGridPoint q j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq]
      calc
        (4 * δ / q) * (∑ j ∈ Finset.range (q ^ 2 + 1), exponentialGridPoint q j) ≤
            (4 * δ / q) * (2 * q) := by gcongr
        _ = 8 * δ := by field_simp; ring

private theorem volume_midpointExceptional_le (q : ℕ) (hq : 0 < q)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    volume (midpointExceptional q δ) ≤ ENNReal.ofReal (8 * δ) := by
  have hmid0 (j : ℕ) : 0 ≤ exponentialMidpoint q j := by
    rw [exponentialMidpoint]
    exact div_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (by norm_num)
  calc
    volume (midpointExceptional q δ) ≤
        ∑ j ∈ Finset.range (q ^ 2),
          volume (multiplicativeWindow (exponentialMidpoint q j) (δ / q)) := by
      exact measure_biUnion_finset_le _ _
    _ = ∑ j ∈ Finset.range (q ^ 2), ENNReal.ofReal
          (exponentialMidpoint q j * Real.exp (δ / q) -
            exponentialMidpoint q j * Real.exp (-(δ / q))) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [multiplicativeWindow, Real.volume_Icc]
    _ ≤ ∑ j ∈ Finset.range (q ^ 2), ENNReal.ofReal
          (4 * exponentialMidpoint q j * δ / q) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal (exp_window_width_le q hq hδ0 hδ1 (hmid0 j))
    _ = ENNReal.ofReal
          (∑ j ∈ Finset.range (q ^ 2), 4 * exponentialMidpoint q j * δ / q) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hmid0 j)) hδ0)
        (Nat.cast_nonneg _)
    _ ≤ ENNReal.ofReal (8 * δ) := by
      apply ENNReal.ofReal_le_ofReal
      have hsum := exponentialMidpoint_sum_le q hq
      have hqr : (0 : ℝ) < q := by exact_mod_cast hq
      have heq : (∑ j ∈ Finset.range (q ^ 2),
          4 * exponentialMidpoint q j * δ / q) =
          (4 * δ / q) *
            (∑ j ∈ Finset.range (q ^ 2), exponentialMidpoint q j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [heq]
      calc
        (4 * δ / q) * (∑ j ∈ Finset.range (q ^ 2), exponentialMidpoint q j) ≤
            (4 * δ / q) * (2 * q) := by gcongr
        _ = 8 * δ := by field_simp; ring

/-- The concrete common boundary exceptional set has the required uniform
measure bound. -/
theorem volume_exponentialExceptionalSet_le (q : ℕ) (hq : 0 < q)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    volume (exponentialExceptionalSet q δ) ≤
      ENNReal.ofReal (Real.exp (-(q : ℝ)) + 16 * δ) := by
  have hinitial : volume (Icc (0 : ℝ) (Real.exp (-(q : ℝ)))) =
      ENNReal.ofReal (Real.exp (-(q : ℝ))) := by
    simp [Real.volume_Icc]
  calc
    volume (exponentialExceptionalSet q δ) ≤
        volume (Icc (0 : ℝ) (Real.exp (-(q : ℝ)))) +
          volume (endpointExceptional q δ) + volume (midpointExceptional q δ) := by
      rw [exponentialExceptionalSet]
      refine (measure_union_le _ _).trans ?_
      gcongr
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(q : ℝ))) +
          ENNReal.ofReal (8 * δ) + ENNReal.ofReal (8 * δ) := by
      rw [hinitial]
      exact add_le_add
        (add_le_add le_rfl (volume_endpointExceptional_le q hq hδ0.le hδ1))
        (volume_midpointExceptional_le q hq hδ0.le hδ1)
    _ = ENNReal.ofReal (Real.exp (-(q : ℝ)) + 16 * δ) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le]
      rw [← ENNReal.ofReal_add (add_nonneg (Real.exp_pos _).le
        (mul_nonneg (by norm_num) hδ0.le))]
      congr 1
      ring
      all_goals positivity

end

end Erdos492Real
