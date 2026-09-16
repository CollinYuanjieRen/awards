import MerLeanExperiment.BackgroundEnergy

open MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace DiskDiscrepancy

theorem continuous_atomicFourier (P : Finset Plane) : Continuous (atomicFourier P) := by
  exact continuous_finsetSum P fun p _ ↦ continuous_pointPhase p

theorem norm_atomicFourier_le (P : Finset Plane) (ξ : Plane) :
    ‖atomicFourier P ξ‖ ≤ P.card := by
  calc
    _ ≤ ∑ p ∈ P, ‖pointPhase p ξ‖ := norm_sum_le _ _
    _ = _ := by simp

theorem integrable_window_norm_sq (a : ℝ) {f : Plane → ℂ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun x : Plane ↦ planeWindow a x * ‖f x‖ ^ 2) := by
  apply (integrable_planeWindow a).mul_bdd (c := M ^ 2) (hf.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM x) 2

theorem integrable_single_interaction (a : ℝ) (p : Plane)
    {g : Plane → ℝ} (hg : Integrable g) :
    Integrable (fun ξ : Plane ↦ planeWindow a ξ *
      (conj (pointPhase p ξ) * (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re) := by
  have hgC : Integrable (fun y : Plane ↦ (g y : ℂ)) := hg.ofReal
  have h := (integrable_window_phase_fourier a p hgC).re
  change Integrable (fun ξ : Plane ↦ (((planeWindow a ξ : ℂ) * pointPhase (-p) ξ) *
    (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re) at h
  simpa only [pointPhase_neg, mul_assoc, Complex.re_ofReal_mul] using h

theorem atomic_interaction_sum (a : ℝ) (P : Finset Plane) (g : Plane → ℂ) (ξ : Plane) :
    planeWindow a ξ * (conj (atomicFourier P ξ) * g ξ).re =
      ∑ p ∈ P, planeWindow a ξ * (conj (pointPhase p ξ) * g ξ).re := by
  simp only [atomicFourier, map_sum, Finset.sum_mul, Complex.re_sum, Finset.mul_sum]

theorem integrable_atomic_interaction (a : ℝ) (P : Finset Plane)
    {g : Plane → ℝ} (hg : Integrable g) :
    Integrable (fun ξ : Plane ↦ planeWindow a ξ *
      (conj (atomicFourier P ξ) * (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re) := by
  simp_rw [atomic_interaction_sum]
  exact integrable_finsetSum P fun p _ ↦ integrable_single_interaction a p hg

theorem atomic_background_interaction_le {a : ℝ} (ha : 0 < a) (P : Finset Plane)
    {g : Plane → ℝ} (hg : Integrable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    (∫ ξ : Plane, planeWindow a ξ *
      (conj (atomicFourier P ξ) * (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re) ≤
        4 * P.card := by
  simp_rw [atomic_interaction_sum]
  rw [integral_finsetSum P (fun p _ ↦ integrable_single_interaction a p hg)]
  calc
    _ ≤ ∑ p ∈ P, (4 : ℝ) :=
      Finset.sum_le_sum fun p _ ↦ window_phase_background_le_four ha p hg hg0 hg1
    _ = _ := by simp [mul_comm]

/-- Subtracting a genuine density between zero and one costs at most eight per point. -/
theorem weighted_discrepancy_energy_lower {a : ℝ} (ha : 0 < a) (P : Finset Plane)
    {g : Plane → ℝ} (hg : Integrable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    (a ^ 2 - 8) * P.card ≤ ∫ ξ : Plane, planeWindow a ξ *
      ‖atomicFourier P ξ - (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ‖ ^ 2 := by
  let G : Plane → ℂ := 𝓕 (fun y : Plane ↦ (g y : ℂ))
  have hgC : Integrable (fun y : Plane ↦ (g y : ℂ)) := hg.ofReal
  have hG : Continuous G := continuous_classicalFourier hgC
  have hGnorm (ξ : Plane) : ‖G ξ‖ ≤ ∫ y : Plane, ‖(g y : ℂ)‖ :=
    norm_classicalFourier_le _ ξ
  have hFint := integrable_window_norm_sq a (continuous_atomicFourier P) (norm_atomicFourier_le P)
  have hDiffint : Integrable (fun ξ : Plane ↦ planeWindow a ξ * ‖atomicFourier P ξ - G ξ‖ ^ 2) :=
    integrable_window_norm_sq a ((continuous_atomicFourier P).sub hG) (fun ξ ↦
      (norm_sub_le _ _).trans (add_le_add (norm_atomicFourier_le P ξ) (hGnorm ξ)))
  have hMixint := integrable_atomic_interaction a P hg
  have hpoint (ξ : Plane) :
      planeWindow a ξ * ‖atomicFourier P ξ‖ ^ 2 -
        2 * (planeWindow a ξ * (conj (atomicFourier P ξ) * G ξ).re) ≤
      planeWindow a ξ * ‖atomicFourier P ξ - G ξ‖ ^ 2 := by
    have hn := norm_sub_sq (𝕜 := ℂ) (atomicFourier P ξ) (G ξ)
    have hn' : ‖atomicFourier P ξ - G ξ‖ ^ 2 = ‖atomicFourier P ξ‖ ^ 2 -
        2 * (conj (atomicFourier P ξ) * G ξ).re + ‖G ξ‖ ^ 2 := by
      simpa only [RCLike.inner_apply', RCLike.re_to_complex] using hn
    rw [hn']
    nlinarith [mul_nonneg (planeWindow_nonneg ha ξ) (sq_nonneg ‖G ξ‖)]
  have hint := integral_mono (hFint.sub (hMixint.const_mul 2)) hDiffint hpoint
  simp only [Pi.sub_apply] at hint
  rw [integral_sub hFint (hMixint.const_mul 2), integral_const_mul] at hint
  have hAtom := atomic_window_energy_lower ha P
  have hBack := atomic_background_interaction_le ha P hg hg0 hg1
  dsimp [G] at hint ⊢
  nlinarith

end DiskDiscrepancy
