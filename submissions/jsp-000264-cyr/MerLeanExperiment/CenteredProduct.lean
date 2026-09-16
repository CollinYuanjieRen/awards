import MerLeanExperiment.CenteredFactor
import MerLeanExperiment.ProductPositivity

namespace ReciprocalSquares

theorem prod_centeredFactor_re_pos
    {ι : Type*} (s : Finset ι) (p t : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (ht : ∀ i ∈ s, |t i| ≤ 1)
    (hsmall : ∑ i ∈ s, |t i| ^ 3 / 3 < Real.log 2) :
    0 < (∏ i ∈ s, centeredFactor (p i) (t i)).re := by
  have hhalf : ∀ i ∈ s, (1 / 2 : ℝ) ≤ (centeredFactor (p i) (t i)).re := by
    intro i hi
    exact half_le_centeredFactor_re _ _ (hp0 i hi) (hp1 i hi) (ht i hi)
  have hre : ∀ i ∈ s, 0 < (centeredFactor (p i) (t i)).re := by
    intro i hi
    have := hhalf i hi
    linarith
  apply prod_re_pos_of_sum_ratio_lt s (fun i => centeredFactor (p i) (t i)) hre
  apply lt_of_le_of_lt _ hsmall
  apply Finset.sum_le_sum
  intro i hi
  apply (div_le_iff₀ (hre i hi)).mpr
  have him := abs_im_centeredFactor_le_cube (p i) (t i) (hp0 i hi) (hp1 i hi)
  have hnonneg : 0 ≤ |t i| ^ 3 / 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left (hhalf i hi) hnonneg
  nlinarith

theorem norm_prod_centeredFactor_le_exp
    {ι : Type*} (s : Finset ι) (p t : ι → ℝ) :
    ‖∏ i ∈ s, centeredFactor (p i) (t i)‖ ≤
      Real.exp (∑ i ∈ s, -p i * (1 - p i) * (1 - Real.cos (t i))) := by
  calc
    ‖∏ i ∈ s, centeredFactor (p i) (t i)‖ ≤
        ∏ i ∈ s, ‖centeredFactor (p i) (t i)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ i ∈ s, Real.exp (-p i * (1 - p i) * (1 - Real.cos (t i))) := by
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      exact norm_centeredFactor_le_exp _ _
    _ = _ := (Real.exp_sum _ _).symm

theorem prod_centeredFactor_factor
    {ι : Type*} (s : Finset ι) (p : ℝ) (t : ι → ℝ) :
    (∏ i ∈ s, centeredFactor p (t i)) =
      Complex.exp (((-p * (∑ i ∈ s, t i) : ℝ) : ℂ) * Complex.I) *
        ∏ i ∈ s, (((1 - p : ℝ) : ℂ) +
          (p : ℂ) * Complex.exp ((t i : ℂ) * Complex.I)) := by
  simp_rw [centeredFactor_factor]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  simp only [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum]

end ReciprocalSquares
