import MerLeanExperiment.CenteredProduct
import Mathlib.Algebra.Order.Round

namespace ReciprocalSquares

theorem eight_sq_le_one_sub_cos_two_pi (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    8 * x ^ 2 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  have hang : |2 * Real.pi * x| ≤ Real.pi := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hg := Real.cos_le_one_sub_mul_cos_sq hang
  have hid : 2 / Real.pi ^ 2 * (2 * Real.pi * x) ^ 2 = 8 * x ^ 2 := by
    field_simp
    ring
  rw [hid] at hg
  linarith

/-- Only the norm is periodic; the centered complex factor itself acquires
a nontrivial phase when an integer is subtracted from the frequency. -/
theorem norm_centeredFactor_residue_le
    (p x : ℝ) (k : ℤ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hx : |x - (k : ℝ)| ≤ (1 / 2 : ℝ)) :
    ‖centeredFactor p (2 * Real.pi * x)‖ ≤
      Real.exp (-8 * p * (1 - p) * (x - (k : ℝ)) ^ 2) := by
  have hcos : Real.cos (2 * Real.pi * x) =
      Real.cos (2 * Real.pi * (x - (k : ℝ))) := by
    convert (Real.cos_sub_int_mul_two_pi (2 * Real.pi * x) k).symm using 1
    congr 1
    ring
  have hg := eight_sq_le_one_sub_cos_two_pi (x - (k : ℝ)) hx
  have hm := mul_le_mul_of_nonneg_left hg (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  calc
    ‖centeredFactor p (2 * Real.pi * x)‖ ≤
        Real.exp (-p * (1 - p) * (1 - Real.cos (2 * Real.pi * x))) :=
      norm_centeredFactor_le_exp _ _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [hcos]
      nlinarith

noncomputable def residueEnergy {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (x i - (round (x i) : ℝ)) ^ 2

theorem norm_prod_centeredFactor_le_energy
    {ι : Type*} (s : Finset ι) (p κ : ℝ) (x : ι → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hκ : κ ≤ p * (1 - p)) :
    ‖∏ i ∈ s, centeredFactor p (2 * Real.pi * x i)‖ ≤
      Real.exp (-8 * κ * residueEnergy s x) := by
  calc
    ‖∏ i ∈ s, centeredFactor p (2 * Real.pi * x i)‖ ≤
        ∏ i ∈ s, ‖centeredFactor p (2 * Real.pi * x i)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i ∈ s, Real.exp (-8 * κ * (x i - (round (x i) : ℝ)) ^ 2) := by
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      apply (norm_centeredFactor_residue_le p (x i) (round (x i)) hp0 hp1
        (abs_sub_round (x i))).trans
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hκ (sq_nonneg (x i - (round (x i) : ℝ)))
      nlinarith
    _ = _ := by rw [← Real.exp_sum, residueEnergy, Finset.mul_sum]

end ReciprocalSquares
