import MerLeanExperiment.FourierBridge
import MerLeanExperiment.GaussianResidue

namespace ReciprocalSquares

theorem centeredProduct_zero (D : Finset ℕ) (p : ℝ) : centeredProduct D p 0 = 1 := by
  simp [centeredProduct, centeredFactor_zero]

theorem norm_centeredProduct_le_energy
    (D : Finset ℕ) (p κ : ℝ) (h : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hκ : κ ≤ p * (1 - p)) :
    ‖centeredProduct D p h‖ ≤
      Real.exp (-8 * κ * residueEnergy D (fun d => (h : ℝ) / (d : ℝ))) := by
  simpa only [centeredProduct, mul_div_assoc] using
    norm_prod_centeredFactor_le_energy D p κ (fun d : ℕ => (h : ℝ) / (d : ℝ))
      hp0 hp1 hκ

theorem norm_centeredProduct_le_of_energy_lower
    (D : Finset ℕ) (p κ L : ℝ) (h : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ p * (1 - p))
    (hL : L ≤ residueEnergy D (fun d => (h : ℝ) / (d : ℝ))) :
    ‖centeredProduct D p h‖ ≤ Real.exp (-8 * κ * L) := by
  apply (norm_centeredProduct_le_energy D p κ h hp0 hp1 hκ).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hL (by nlinarith)

/-- A nonnegative frequency region containing the unit term dominates a small
total norm on its complement. -/
theorem real_sum_ge_half_of_good_bad
    {ι : Type*} [DecidableEq ι] (s G : Finset ι) (zero : ι) (f : ι → ℂ)
    (hG : G ⊆ s) (hzero : zero ∈ G) (hfzero : (f zero).re = 1)
    (hgood : ∀ i ∈ G, 0 ≤ (f i).re)
    (hbad : ∑ i ∈ s \ G, ‖f i‖ ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ (∑ i ∈ s, f i).re := by
  have hgoodSum : (1 : ℝ) ≤ ∑ i ∈ G, (f i).re := by
    rw [← hfzero]
    exact Finset.single_le_sum hgood hzero
  have hbadSum : -(1 / 2 : ℝ) ≤ ∑ i ∈ s \ G, (f i).re := by
    have hpoint : ∑ i ∈ s \ G, -‖f i‖ ≤ ∑ i ∈ s \ G, (f i).re := by
      apply Finset.sum_le_sum
      intro i _
      exact neg_le_of_abs_le (Complex.abs_re_le_norm (f i))
    rw [Finset.sum_neg_distrib] at hpoint
    linarith
  have hsplit := Finset.sum_sdiff hG (f := fun i => (f i).re)
  have hre : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by simp
  rw [hre]
  linarith

end ReciprocalSquares
