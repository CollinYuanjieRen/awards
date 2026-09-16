import MerLeanExperiment.AngularAverage

open MeasureTheory

namespace DiskDiscrepancy

noncomputable section

/-- The radial expression which the separate disk-Fourier bridge identifies
with the Fourier transform of a disk. -/
def radialProfile (rho r : ℝ) : ℝ :=
  if rho = 0 then Real.pi * r ^ 2
  else angularPrimitive (2 * Real.pi * rho * r) / (2 * Real.pi * rho ^ 2)

theorem continuous_radialProfile (rho : ℝ) : Continuous (radialProfile rho) := by
  by_cases h : rho = 0
  · subst rho
    rw [show radialProfile 0 = (fun r : ℝ ↦ Real.pi * r ^ 2) by
      funext r
      simp [radialProfile]]
    fun_prop
  · rw [show radialProfile rho = (fun r : ℝ ↦
        angularPrimitive (2 * Real.pi * rho * r) / (2 * Real.pi * rho ^ 2)) by
      funext r
      simp [radialProfile, h]]
    exact (continuous_angularPrimitive.comp
      (continuous_const.mul continuous_id)).div_const _

/-- High-frequency radius-average estimate for the actual angular primitive. -/
theorem radialProfile_high_frequency {R rho : ℝ} (hR : 0 < R) (hrho : 0 ≤ rho)
    (hz : 128 ≤ 2 * Real.pi * rho * R) :
    R / (256 * Real.pi * rho ^ 3) ≤
      (1 / R) * ∫ r in 0..R, radialProfile rho r ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrho_pos : 0 < rho := by
    by_contra hn
    have : rho = 0 := le_antisymm (le_of_not_gt hn) hrho
    simp [this] at hz
    linarith
  have hrho0 : rho ≠ 0 := ne_of_gt hrho_pos
  let k : ℝ := 2 * Real.pi * rho
  have hk : 0 < k := by dsimp [k]; positivity
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hangular : (k * R) ^ 2 / 128 ≤
      ∫ t in 0..k * R, angularPrimitive t ^ 2 := by
    apply angularPrimitive_square_integral_lower
    simpa [k, mul_assoc] using hz
  have hchange : (∫ r in 0..R, angularPrimitive (k * r) ^ 2) =
      k⁻¹ * ∫ t in 0..k * R, angularPrimitive t ^ 2 := by
    simpa using (intervalIntegral.integral_comp_mul_left
      (fun t : ℝ ↦ angularPrimitive t ^ 2) hk0 (a := 0) (b := R))
  have hprofile : (∫ r in 0..R, radialProfile rho r ^ 2) =
      (1 / (2 * Real.pi * rho ^ 2) ^ 2) *
        ∫ r in 0..R, angularPrimitive (k * r) ^ 2 := by
    simp only [radialProfile, hrho0, ↓reduceIte, div_pow]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const]
    dsimp [k]
    ring
  rw [hprofile, hchange]
  have hscale : 0 ≤ (1 / R) * (1 / (2 * Real.pi * rho ^ 2) ^ 2) * k⁻¹ := by positivity
  have hm := mul_le_mul_of_nonneg_left hangular hscale
  dsimp [k] at hm ⊢
  field_simp [ne_of_gt hR, hrho0, ne_of_gt hpi] at hm ⊢
  nlinarith

/-- Low-frequency radius-average estimate, including zero frequency. -/
theorem radialProfile_low_frequency {R rho : ℝ} (hR : 0 < R) (hrho : 0 ≤ rho)
    (hz : 2 * Real.pi * rho * R ≤ 128) :
    Real.pi ^ 2 * R ^ 4 / (20 * 128 ^ 5) ≤
      (1 / R) * ∫ r in 0..R, radialProfile rho r ^ 2 := by
  let L : ℝ := R / 128
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLR : L ≤ R := by dsimp [L]; nlinarith
  have hprof_int : IntervalIntegrable (fun r ↦ radialProfile rho r ^ 2) volume 0 R :=
    ((continuous_radialProfile rho).pow 2).intervalIntegrable _ _
  have hrestrict : (∫ r in 0..L, radialProfile rho r ^ 2) ≤
      ∫ r in 0..R, radialProfile rho r ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hL hLR
      (Filter.Eventually.of_forall fun r ↦ sq_nonneg (radialProfile rho r)) hprof_int
  have hpoint : ∀ r ∈ Set.Icc (0 : ℝ) L,
      Real.pi ^ 2 * r ^ 4 / 4 ≤ radialProfile rho r ^ 2 := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1
    by_cases hrho0 : rho = 0
    · simp [radialProfile, hrho0]
      nlinarith [sq_nonneg (Real.pi * r ^ 2)]
    · have hrho_pos : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hrho0)
      have harg0 : 0 ≤ 2 * Real.pi * rho * r := by positivity
      have harg1 : 2 * Real.pi * rho * r ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hr.2 (by positivity : 0 ≤ 2 * Real.pi * rho)
        dsimp [L] at this
        nlinarith
      have hA := sq_div_four_le_angularPrimitive harg0 harg1
      have hden : 0 < 2 * Real.pi * rho ^ 2 := by positivity
      have hp : Real.pi * r ^ 2 / 2 ≤ radialProfile rho r := by
        simp only [radialProfile, hrho0, ↓reduceIte]
        apply (le_div_iff₀ hden).2
        calc
          Real.pi * r ^ 2 / 2 * (2 * Real.pi * rho ^ 2) =
              (2 * Real.pi * rho * r) ^ 2 / 4 := by ring
          _ ≤ angularPrimitive (2 * Real.pi * rho * r) := hA
      have hp0 : 0 ≤ radialProfile rho r := le_trans (by positivity) hp
      nlinarith [sq_nonneg (radialProfile rho r - Real.pi * r ^ 2 / 2)]
  have hminor_int : IntervalIntegrable (fun r : ℝ ↦ Real.pi ^ 2 * r ^ 4 / 4)
      volume 0 L :=
    ((continuous_const.mul (continuous_id.pow 4)).div_const 4).intervalIntegrable _ _
  have hmono : (∫ r in 0..L, Real.pi ^ 2 * r ^ 4 / 4) ≤
      ∫ r in 0..L, radialProfile rho r ^ 2 :=
    intervalIntegral.integral_mono_on hL hminor_int
      (((continuous_radialProfile rho).pow 2).intervalIntegrable _ _) hpoint
  have hpoly : (∫ r in 0..L, Real.pi ^ 2 * r ^ 4 / 4) =
      Real.pi ^ 2 * L ^ 5 / 20 := by
    norm_num
    ring
  rw [hpoly] at hmono
  have htotal : Real.pi ^ 2 * L ^ 5 / 20 ≤
      ∫ r in 0..R, radialProfile rho r ^ 2 := hmono.trans hrestrict
  dsimp [L] at htotal ⊢
  have hR0 : R ≠ 0 := ne_of_gt hR
  field_simp [hR0] at htotal ⊢
  nlinarith [Real.pi_pos.le]

/-- Universal constant in the radial-profile average bound. -/
def radialProfileConstant : ℝ :=
  min (1 / (256 * Real.pi)) (Real.pi ^ 2 / (20 * 128 ^ 5))

theorem radialProfileConstant_pos : 0 < radialProfileConstant := by
  unfold radialProfileConstant
  exact lt_min (by positivity) (by positivity)

/-- Uniform radius-average lower bound for the actual radial profile. -/
theorem radialProfile_average_lower {R rho : ℝ} (hR : 0 < R) (hrho : 0 ≤ rho) :
    radialProfileConstant * R ^ 4 / (1 + R * rho) ^ 3 ≤
      (1 / R) * ∫ r in 0..R, radialProfile rho r ^ 2 := by
  have hden : 0 < (1 + R * rho) ^ 3 := by positivity
  by_cases hz : 128 ≤ 2 * Real.pi * rho * R
  · have hhigh := radialProfile_high_frequency hR hrho hz
    have hrho_pos : 0 < rho := by
      by_contra hn
      have hrho0 : rho = 0 := le_antisymm (le_of_not_gt hn) hrho
      simp [hrho0] at hz
      linarith
    have hc : radialProfileConstant ≤ 1 / (256 * Real.pi) :=
      min_le_left _ _
    have hx : 0 ≤ R * rho := by positivity
    have hcubes : (R * rho) ^ 3 ≤ (1 + R * rho) ^ 3 := by
      have hs : 0 ≤ 1 + 3 * (R * rho) + 3 * (R * rho) ^ 2 := by positivity
      nlinarith
    have hcompare : radialProfileConstant * R ^ 4 / (1 + R * rho) ^ 3 ≤
        R / (256 * Real.pi * rho ^ 3) := by
      have hpi := Real.pi_pos
      have hrho0 : rho ≠ 0 := ne_of_gt hrho_pos
      have hR4 : 0 ≤ R ^ 4 := by positivity
      have hfirst : radialProfileConstant * R ^ 4 / (1 + R * rho) ^ 3 ≤
          (1 / (256 * Real.pi)) * R ^ 4 / (1 + R * rho) ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hR4) hden.le
      have hsecond : (1 / (256 * Real.pi)) * R ^ 4 / (1 + R * rho) ^ 3 ≤
          R / (256 * Real.pi * rho ^ 3) := by
        apply (div_le_iff₀ hden).2
        field_simp [hrho0, ne_of_gt hpi]
        nlinarith
      exact hfirst.trans hsecond
    exact hcompare.trans hhigh
  · have hlow := radialProfile_low_frequency hR hrho (le_of_not_ge hz)
    have hc : radialProfileConstant ≤ Real.pi ^ 2 / (20 * 128 ^ 5) :=
      min_le_right _ _
    have hden_one : 1 ≤ (1 + R * rho) ^ 3 := by
      nlinarith [sq_nonneg (R * rho), mul_nonneg hR.le hrho]
    have hleft : radialProfileConstant * R ^ 4 / (1 + R * rho) ^ 3 ≤
        Real.pi ^ 2 * R ^ 4 / (20 * 128 ^ 5) := by
      have hR4 : 0 ≤ R ^ 4 := by positivity
      have hfirst : radialProfileConstant * R ^ 4 / (1 + R * rho) ^ 3 ≤
          (Real.pi ^ 2 / (20 * 128 ^ 5)) * R ^ 4 / (1 + R * rho) ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hR4) hden.le
      have hconstpos : 0 ≤ (Real.pi ^ 2 / (20 * 128 ^ 5)) * R ^ 4 := by positivity
      have hsecond : (Real.pi ^ 2 / (20 * 128 ^ 5)) * R ^ 4 /
          (1 + R * rho) ^ 3 ≤ Real.pi ^ 2 * R ^ 4 / (20 * 128 ^ 5) := by
        rw [div_le_iff₀ hden]
        nlinarith
      exact hfirst.trans hsecond
    exact hleft.trans hlow

end

end DiskDiscrepancy
