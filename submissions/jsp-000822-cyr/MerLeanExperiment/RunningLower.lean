import MerLeanExperiment.LowerEnergy
import MerLeanExperiment.PackingDensity
import MerLeanExperiment.Qualitative

namespace DiskDiscrepancy

/-- The scalar contradiction after actual spectral/spatial comparison and finite packing. -/
theorem small_uniform_error_impossible {S : Set Plane} (hS : Admissible S)
    {R d β : ℝ} (hR : 2 ≤ R) (hβ : β = radialProfileConstant / 686)
    (_hd0 : 0 < d) (hd1 : d ≤ 1) (hdβ : d ^ 2 ≤ β / 16)
    (hbound : ∀ x : Plane, ∀ r : ℝ, 0 < r → r ≤ R →
      discrepancy S x r ≤ d * Real.sqrt R) : False := by
  have hc := radialProfileConstant_pos
  have hβpos : 0 < β := by rw [hβ]; exact div_pos radialProfileConstant_pos (by norm_num)
  have hRpos : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hsqrt := Real.sq_sqrt hRpos.le
  have hsqrtle : Real.sqrt R ≤ R := Real.sqrt_le_self_iff.mpr (Or.inr hR1)
  have hD : d * Real.sqrt R ≤ R ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hd1 (Real.sqrt_nonneg R)
    nlinarith
  have hcount (x : Plane) : R ^ 2 ≤ (pointCount S x R : ℝ) := by
    have h := hbound x R hRpos le_rfl
    change |(pointCount S x R : ℝ) - Real.pi * R ^ 2| ≤ d * Real.sqrt R at h
    have hleft := (abs_le.mp h).1
    have hpi := mul_le_mul_of_nonneg_right (le_of_lt Real.pi_gt_three) (sq_nonneg R)
    nlinarith
  let C : ℝ := 16 * (2 * Real.pi + 1) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (C * R ^ 3 / β))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnNat : 1 ≤ n := by exact_mod_cast hn1.le
  have hnlarge : C * R ^ 3 / β < n := (le_max_right _ _).trans_lt hn
  have hnprod : C * R ^ 3 < (n : ℝ) * β := (div_lt_iff₀ hβpos).mp hnlarge
  let M : ℝ := 4 * R * n
  have hM : R < M := by dsimp [M]; nlinarith
  have hMpos : 0 < M := hRpos.trans hM
  have hpack := cutoffPoints_card_lower_of_disk_counts hS hRpos hnNat hcount
  change M ^ 2 / 16 ≤ ((cutoffPoints S hS M).card : ℝ) at hpack
  have hcomparison := cutoff_energy_comparison hS hR1 hM hD hbound
  have hscaled := mul_le_mul_of_nonneg_left hpack
    (by positivity : 0 ≤ (8 * radialProfileConstant / 343) * R)
  have hid : (8 * radialProfileConstant / 343) * R * (M ^ 2 / 16) = β * R * M ^ 2 := by
    rw [hβ]; ring
  rw [hid] at hscaled
  have hlower : β * R * M ^ 2 ≤ 4 * M ^ 2 * (d * Real.sqrt R) ^ 2 + C * M * R ^ 5 :=
    hscaled.trans hcomparison
  have hDsq : (d * Real.sqrt R) ^ 2 = d ^ 2 * R := by rw [mul_pow, hsqrt]
  have hfirst : 4 * M ^ 2 * (d * Real.sqrt R) ^ 2 ≤ β * R * M ^ 2 / 4 := by
    rw [hDsq]
    have h := mul_le_mul_of_nonneg_left hdβ (by positivity : 0 ≤ 4 * M ^ 2 * R)
    nlinarith [h]
  have hMlarge : 4 * C * R ^ 4 < β * M := by
    have h := mul_lt_mul_of_pos_left hnprod (by positivity : 0 < 4 * R)
    dsimp [M]
    nlinarith [h]
  have hsecond : C * M * R ^ 5 < β * R * M ^ 2 / 4 := by
    have h := mul_lt_mul_of_pos_right hMlarge (by positivity : 0 < M * R)
    nlinarith [h]
  have hpositive : 0 < β * R * M ^ 2 := by positivity
  linarith

/-- Beck's running-radius square-root lower bound for every admissible planar point set. -/
theorem runningLower : RunningLowerBound := by
  let β : ℝ := radialProfileConstant / 686
  let d : ℝ := min 1 (Real.sqrt β / 4)
  have hβ : 0 < β := div_pos radialProfileConstant_pos (by norm_num)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdβ : d ^ 2 ≤ β / 16 := by
    have h := pow_le_pow_left₀ hd.le (min_le_right 1 (Real.sqrt β / 4)) 2
    have hs := Real.sq_sqrt hβ.le
    dsimp [d] at h ⊢
    nlinarith
  refine ⟨d, hd, 2, le_rfl, fun R hR S hS ↦ ?_⟩
  by_contra hn
  push Not at hn
  have hbound : ∀ x : Plane, ∀ r : ℝ, 0 < r → r ≤ R →
      discrepancy S x r ≤ d * Real.sqrt R := fun x r hr hrR ↦ (hn x r hr hrR).le
  exact small_uniform_error_impossible hS hR rfl hd hd1 hdβ hbound

/-- No point set has a finite uniform discrepancy bound on all closed disks. -/
theorem noUniformDiskBound : NoUniformDiskBound :=
  noUniformDiskBound_of_runningLower runningLower

end DiskDiscrepancy
