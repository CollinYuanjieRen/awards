import MerLeanExperiment.OscillatorEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory

namespace DiskDiscrepancy

noncomputable section

/-- A lower bound for the `v²` mass of a bounded rational oscillator on `[z/2,z]`. -/
theorem oscillator_integral_sq_v_lower {u v : ℝ → ℝ} (hu_cont : ContinuousOn u (Ioi 0))
    (hv_cont : ContinuousOn v (Ioi 0))
    (hu : ∀ t : ℝ, 0 < t → HasDerivAt u (v t) t)
    (hv : ∀ t : ℝ, 0 < t → HasDerivAt v (-oscillatorCoeff t * u t) t)
    (henergy : ∀ t : ℝ, 1 ≤ t →
      1 / 4 ≤ u t ^ 2 + v t ^ 2 ∧ u t ^ 2 + v t ^ 2 ≤ 7 / 2)
    {z : ℝ} (hz : 128 ≤ z) :
    z / 16 - 7 / 2 ≤ ∫ t in z / 2..z, v t ^ 2 := by
  let a : ℝ := z / 2
  have hz_pos : 0 < z := lt_of_lt_of_le (by norm_num) hz
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have ha_one : 1 ≤ a := by dsimp [a]; linarith
  have hab : a ≤ z := by dsimp [a]; linarith
  have hu_cont_Icc : ContinuousOn u (Icc a z) :=
    hu_cont.mono fun _ ht ↦ ha_pos.trans_le ht.1
  have hv_cont_Icc : ContinuousOn v (Icc a z) :=
    hv_cont.mono fun _ ht ↦ ha_pos.trans_le ht.1
  have hu_sq_int : IntervalIntegrable (fun t ↦ u t ^ 2) volume a z :=
    (hu_cont_Icc.pow 2).intervalIntegrable_of_Icc hab
  have hv_sq_int : IntervalIntegrable (fun t ↦ v t ^ 2) volume a z :=
    (hv_cont_Icc.pow 2).intervalIntegrable_of_Icc hab
  have hsum_int : IntervalIntegrable (fun t ↦ u t ^ 2 + v t ^ 2) volume a z :=
    hu_sq_int.add hv_sq_int
  have henergy_int : z / 8 ≤ ∫ t in a..z, u t ^ 2 + v t ^ 2 := by
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 / 4 : ℝ)) volume a z :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hab hconst hsum_int fun t ht ↦
      (henergy t (ha_one.trans ht.1)).1
    have heq : (z - z / 2) / 4 = z / 8 := by ring
    dsimp [a] at hmono ⊢
    norm_num at hmono
    rw [heq] at hmono
    exact hmono
  have hprod_deriv : ∀ t ∈ Icc a z,
      HasDerivAt (fun s ↦ u s * v s) (v t ^ 2 - oscillatorCoeff t * u t ^ 2) t := by
    intro t ht
    have ht_pos : 0 < t := ha_pos.trans_le ht.1
    have ht0 : t ≠ 0 := ne_of_gt ht_pos
    have hraw : HasDerivAt (fun s ↦ u s * v s)
        (v t * v t + u t * (-oscillatorCoeff t * u t)) t :=
      (hu t ht_pos).mul (hv t ht_pos)
    have heq : v t * v t + u t * (-oscillatorCoeff t * u t) =
        v t ^ 2 - oscillatorCoeff t * u t ^ 2 := by ring
    exact hraw.congr_deriv heq
  have hq_cont : ContinuousOn oscillatorCoeff (Icc a z) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha_pos.trans_le ht.1)
    apply ContinuousAt.continuousWithinAt
    unfold oscillatorCoeff
    exact continuousAt_const.add
      (continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 2))
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht0)))
  have hderiv_int : IntervalIntegrable
      (fun t ↦ v t ^ 2 - oscillatorCoeff t * u t ^ 2) volume a z := by
    exact ((hv_cont_Icc.pow 2).sub
      (hq_cont.mul (hu_cont_Icc.pow 2))).intervalIntegrable_of_Icc hab
  have hftc : (∫ t in a..z, v t ^ 2 - oscillatorCoeff t * u t ^ 2) =
      u z * v z - u a * v a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (hu_cont_Icc.mul hv_cont_Icc)
      (fun t ht ↦ hprod_deriv t ⟨ht.1.le, ht.2.le⟩) hderiv_int
  have hdiff_int : IntervalIntegrable (fun t ↦ v t ^ 2 - u t ^ 2) volume a z :=
    hv_sq_int.sub hu_sq_int
  have hderiv_le : (∫ t in a..z, v t ^ 2 - oscillatorCoeff t * u t ^ 2) ≤
      ∫ t in a..z, v t ^ 2 - u t ^ 2 := by
    apply intervalIntegral.integral_mono_on hab hderiv_int hdiff_int
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha_pos.trans_le ht.1)
    have hq := one_le_oscillatorCoeff ht0
    nlinarith [sq_nonneg (u t)]
  have huv_bound : ∀ t : ℝ, 1 ≤ t → |u t * v t| ≤ 7 / 4 := by
    intro t ht
    have hE := (henergy t ht).2
    have htwo : 2 * |u t * v t| ≤ u t ^ 2 + v t ^ 2 := by
      rw [abs_mul]
      simpa [sq_abs, mul_assoc] using two_mul_le_add_sq |u t| |v t|
    linarith
  have hboundary : -(7 / 2) ≤ u z * v z - u a * v a := by
    have hz_uv := huv_bound z (by linarith)
    have ha_uv := huv_bound a ha_one
    have hzl := neg_le_of_abs_le hz_uv
    have hal := le_of_abs_le ha_uv
    linarith
  rw [intervalIntegral.integral_add hu_sq_int hv_sq_int] at henergy_int
  rw [intervalIntegral.integral_sub hv_sq_int hu_sq_int] at hderiv_le
  rw [hftc] at hderiv_le
  linarith

/-- Integrated-square lower bound for an oscillator primitive.

This supporting lemma remains conditional on the oscillator and primitive identities. The
angular-kernel development must instantiate those hypotheses before the disk theorem uses it. -/
theorem oscillator_integral_sq_lower {u v A : ℝ → ℝ} (hu_cont : ContinuousOn u (Ioi 0))
    (hv_cont : ContinuousOn v (Ioi 0)) (hA_cont : Continuous A)
    (hu : ∀ t : ℝ, 0 < t → HasDerivAt u (v t) t)
    (hv : ∀ t : ℝ, 0 < t → HasDerivAt v (-oscillatorCoeff t * u t) t)
    (henergy : ∀ t : ℝ, 1 ≤ t →
      1 / 4 ≤ u t ^ 2 + v t ^ 2 ∧ u t ^ 2 + v t ^ 2 ≤ 7 / 2)
    (hA : ∀ t : ℝ, 0 < t → A t = Real.sqrt t * (u t / (2 * t) - v t))
    {z : ℝ} (hz : 128 ≤ z) : z ^ 2 / 128 ≤ ∫ t in 0..z, A t ^ 2 := by
  let a : ℝ := z / 2
  have hz_pos : 0 < z := lt_of_lt_of_le (by norm_num) hz
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have ha_one : 1 ≤ a := by dsimp [a]; linarith
  have hab : a ≤ z := by dsimp [a]; linarith
  have hv_cont_Icc : ContinuousOn v (Icc a z) :=
    hv_cont.mono fun _ ht ↦ ha_pos.trans_le ht.1
  have hv_mass : z / 16 - 7 / 2 ≤ ∫ t in a..z, v t ^ 2 :=
    oscillator_integral_sq_v_lower hu_cont hv_cont hu hv henergy hz
  have hA_sq_int : IntervalIntegrable (fun t ↦ A t ^ 2) volume a z :=
    hA_cont.pow 2 |>.intervalIntegrable _ _
  have hv_sq_int : IntervalIntegrable (fun t ↦ v t ^ 2) volume a z :=
    (hv_cont_Icc.pow 2).intervalIntegrable_of_Icc hab
  have hminor_int : IntervalIntegrable (fun t ↦ z / 4 * v t ^ 2 - 7 / (4 * z))
      volume a z := (hv_sq_int.const_mul _).sub intervalIntegrable_const
  have hpoint : ∀ t ∈ Icc a z, z / 4 * v t ^ 2 - 7 / (4 * z) ≤ A t ^ 2 := by
    intro t ht
    have ht_pos : 0 < t := ha_pos.trans_le ht.1
    have ht_one : 1 ≤ t := ha_one.trans ht.1
    have hE := (henergy t ht_one).2
    have hsqrt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht_pos.le
    let w := u t / (2 * t)
    have halg : v t ^ 2 / 2 - w ^ 2 ≤ (w - v t) ^ 2 := by
      nlinarith [sq_nonneg (v t - 2 * w)]
    rw [hA t ht_pos, mul_pow, hsqrt]
    have ht_lower : z / 2 ≤ t := ht.1
    have hu_sq : u t ^ 2 ≤ 7 / 2 := by nlinarith [sq_nonneg (v t)]
    have hz0 : z ≠ 0 := ne_of_gt hz_pos
    have ht0 : t ≠ 0 := ne_of_gt ht_pos
    have hw : w ^ 2 = u t ^ 2 / (4 * t ^ 2) := by
      dsimp [w]
      field_simp [ht0]
      ring
    have hbase : t * (v t ^ 2 / 2 - u t ^ 2 / (4 * t ^ 2)) ≤
        t * (u t / (2 * t) - v t) ^ 2 := by
      rw [← hw]
      exact mul_le_mul_of_nonneg_left halg ht_pos.le
    have hzv : z / 4 * v t ^ 2 ≤ t / 2 * v t ^ 2 := by
      nlinarith [sq_nonneg (v t)]
    have hu_term : u t ^ 2 / (4 * t) ≤ 7 / (4 * z) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * t) (by positivity : 0 < 4 * z)).2
      nlinarith [mul_nonneg (sq_nonneg (u t)) hz_pos.le]
    have hbase' : t / 2 * v t ^ 2 - u t ^ 2 / (4 * t) ≤
        t * (u t / (2 * t) - v t) ^ 2 := by
      calc
        t / 2 * v t ^ 2 - u t ^ 2 / (4 * t) =
            t * (v t ^ 2 / 2 - u t ^ 2 / (4 * t ^ 2)) := by
              field_simp [ht0]
        _ ≤ t * (u t / (2 * t) - v t) ^ 2 := hbase
    nlinarith
  have hinterval : (∫ t in a..z, z / 4 * v t ^ 2 - 7 / (4 * z)) ≤
      ∫ t in a..z, A t ^ 2 :=
    intervalIntegral.integral_mono_on hab hminor_int hA_sq_int hpoint
  have hrestrict : (∫ t in a..z, A t ^ 2) ≤ ∫ t in 0..z, A t ^ 2 := by
    exact intervalIntegral.integral_mono_interval (by linarith) hab le_rfl
      (Filter.Eventually.of_forall fun t ↦ sq_nonneg (A t))
      (hA_cont.pow 2 |>.intervalIntegrable 0 z)
  rw [intervalIntegral.integral_sub (hv_sq_int.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul] at hinterval
  norm_num [a] at hinterval
  have hz0 : z ≠ 0 := ne_of_gt hz_pos
  have hmass_scaled := mul_le_mul_of_nonneg_left hv_mass (by positivity : 0 ≤ z / 4)
  have hconsteq : (z - z / 2) * 7 / (4 * z) = 7 / 8 := by
    field_simp [hz0]
    ring
  rw [hconsteq] at hinterval
  have hmasseq : z / 4 * (z / 16 - 7 / 2) = z ^ 2 / 64 - 7 * z / 8 := by ring
  rw [hmasseq] at hmass_scaled
  have hcoarse : z ^ 2 / 64 - 7 * z / 8 - 7 / 8 ≤ ∫ t in a..z, A t ^ 2 := by
    linarith
  have harith : z ^ 2 / 128 ≤ z ^ 2 / 64 - 7 * z / 8 - 7 / 8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (by linarith : 0 ≤ z + 112)]
  exact harith.trans (hcoarse.trans hrestrict)

end

end DiskDiscrepancy
