import MerLeanExperiment.AtomicEnergy

open MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace DiskDiscrepancy

theorem continuous_classicalFourier {f : Plane → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f : Plane → ℂ) := by
  change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Plane) f)
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ : Plane →L[ℝ] Plane →L[ℝ] ℝ).continuous₂ hf

theorem norm_classicalFourier_le (f : Plane → ℂ) (ξ : Plane) :
    ‖(𝓕 f : Plane → ℂ) ξ‖ ≤ ∫ y : Plane, ‖f y‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem fourier_pairing {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ y : Plane, (𝓕 f : Plane → ℂ) y * g y) = ∫ ξ : Plane, f ξ * (𝓕 g : Plane → ℂ) ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    Real.continuous_fourierChar (μ := volume) (ν := volume) (L := innerₗ Plane)
    (innerSL ℝ : Plane →L[ℝ] Plane →L[ℝ] ℝ).continuous₂ hf hg
  have hf_eq : (𝓕 f : Plane → ℂ) = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Plane) f := funext (Real.fourier_eq f)
  have hg_eq : (𝓕 g : Plane → ℂ) = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Plane) g := funext (Real.fourier_eq g)
  rw [hf_eq, hg_eq]
  simpa only [flip_innerₗ, smul_eq_mul] using h

/-- Modulating the frequency window translates its positive spatial kernel. -/
theorem fourier_modulated_window {a : ℝ} (ha : 0 < a) (p y : Plane) :
    𝓕 (fun ξ : Plane ↦ (planeWindow a ξ : ℂ) * pointPhase (-p) ξ) y =
      (planeKernel a (y - p) : ℂ) := by
  rw [Real.fourier_eq']
  change (∫ ξ : Plane, pointPhase y ξ * ((planeWindow a ξ : ℂ) * pointPhase (-p) ξ)) = _
  calc
    _ = ∫ ξ : Plane, (planeWindow a ξ : ℂ) * pointPhase (y - p) ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [sub_eq_add_neg, pointPhase_add]
      ring
    _ = _ := integral_weighted_pointPhase ha (y - p)

theorem integrable_window_phase_fourier (a : ℝ) (p : Plane)
    {g : Plane → ℂ} (hg : Integrable g) :
    Integrable (fun ξ : Plane ↦
      ((planeWindow a ξ : ℂ) * pointPhase (-p) ξ) * (𝓕 g : Plane → ℂ) ξ) := by
  apply (integrable_weighted_pointPhase a (-p)).mul_bdd
    (c := ∫ y : Plane, ‖g y‖) (continuous_classicalFourier hg).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_classicalFourier_le g)

/-- Fourier pairing reduces the interaction with a density to a translated positive kernel. -/
theorem window_phase_background_identity {a : ℝ} (ha : 0 < a) (p : Plane)
    {g : Plane → ℝ} (hg : Integrable g) :
    (∫ ξ : Plane, ((planeWindow a ξ : ℂ) * pointPhase (-p) ξ) *
      (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ) =
        ((∫ y : Plane, planeKernel a (y - p) * g y : ℝ) : ℂ) := by
  have hgC : Integrable (fun y : Plane ↦ (g y : ℂ)) := hg.ofReal
  calc
    _ = ∫ y : Plane,
        (𝓕 (fun ξ : Plane ↦ (planeWindow a ξ : ℂ) * pointPhase (-p) ξ) : Plane → ℂ) y * (g y : ℂ) :=
      (fourier_pairing (integrable_weighted_pointPhase a (-p)) hgC).symm
    _ = _ := by
      simp_rw [fourier_modulated_window ha]
      rw [← integral_complex_ofReal]
      simp only [Complex.ofReal_mul]

/-- A density between zero and one contributes at most the kernel mass per point. -/
theorem window_phase_background_le_four {a : ℝ} (ha : 0 < a) (p : Plane)
    {g : Plane → ℝ} (hg : Integrable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    (∫ ξ : Plane, (planeWindow a ξ) *
      (conj (pointPhase p ξ) * (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re) ≤ 4 := by
  have hk : Integrable (fun y : Plane ↦ planeKernel a (y - p)) :=
    (integrable_planeKernel ha).comp_sub_right p
  have hkg : Integrable (fun y : Plane ↦ planeKernel a (y - p) * g y) := by
    apply hk.mul_bdd (c := 1) hg.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 y)] using hg1 y
  have hreal : (∫ ξ : Plane, (planeWindow a ξ) *
      (conj (pointPhase p ξ) * (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re) =
      ∫ y : Plane, planeKernel a (y - p) * g y := by
    have hgC : Integrable (fun y : Plane ↦ (g y : ℂ)) := hg.ofReal
    calc
      _ = ∫ ξ : Plane, (((planeWindow a ξ : ℂ) * pointPhase (-p) ξ) *
          (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        simp only [pointPhase_neg, mul_assoc, Complex.re_ofReal_mul]
      _ = (∫ ξ : Plane, ((planeWindow a ξ : ℂ) * pointPhase (-p) ξ) *
          (𝓕 (fun y : Plane ↦ (g y : ℂ)) : Plane → ℂ) ξ).re :=
        integral_re (𝕜 := ℂ) (integrable_window_phase_fourier a p hgC)
      _ = _ := by rw [window_phase_background_identity ha p hg, Complex.ofReal_re]
  rw [hreal]
  calc
    _ ≤ ∫ y : Plane, planeKernel a (y - p) :=
      integral_mono hkg hk (fun y ↦
        mul_le_of_le_one_right (planeKernel_nonneg ha (y - p)) (hg1 y))
    _ = ∫ y : Plane, planeKernel a y := integral_sub_right_eq_self _ p
    _ ≤ 4 := integral_planeKernel_le_four ha

end DiskDiscrepancy
