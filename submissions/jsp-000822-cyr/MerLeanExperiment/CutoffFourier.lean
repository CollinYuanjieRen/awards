import MerLeanExperiment.BoxGeometry
import MerLeanExperiment.DiskFourier
import MerLeanExperiment.FourierPlancherel

open MeasureTheory
open scoped FourierTransform ComplexConjugate Convolution

namespace DiskDiscrepancy

theorem integrable_phase_mul {f : Plane → ℂ} (hf : Integrable f) (ξ : Plane) :
    Integrable (fun x : Plane ↦ pointPhase ξ x * f x) := by
  apply hf.bdd_mul (c := 1) (continuous_pointPhase ξ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ (norm_pointPhase ξ x).le

theorem fourier_sub_integrable {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ξ : Plane) :
    (𝓕 (fun x ↦ f x - g x) : Plane → ℂ) ξ = (𝓕 f : Plane → ℂ) ξ - (𝓕 g : Plane → ℂ) ξ := by
  simp only [Real.fourier_eq', smul_eq_mul, mul_sub]
  exact integral_sub (integrable_phase_mul hf ξ) (integrable_phase_mul hg ξ)

theorem fourier_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Plane → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) (ξ : Plane) :
    (𝓕 (fun x ↦ ∑ i ∈ s, f i x) : Plane → ℂ) ξ = ∑ i ∈ s, (𝓕 (f i) : Plane → ℂ) ξ := by
  simp only [Real.fourier_eq', smul_eq_mul, Finset.mul_sum]
  exact integral_finsetSum s fun i hi ↦ integrable_phase_mul (hf i hi) ξ

theorem fourier_translate (f : Plane → ℂ) (p ξ : Plane) :
    (𝓕 (fun x : Plane ↦ f (x - p)) : Plane → ℂ) ξ =
      pointPhase p ξ * (𝓕 f : Plane → ℂ) ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    volume (innerₗ Plane) f (-p)) ξ
  have hphase : (Real.fourierChar (inner ℝ (-p) ξ) : ℂ) = pointPhase p ξ := by
    simp only [Real.fourierChar_apply, inner_neg_left, pointPhase]
    rw [real_inner_comm p ξ]
    congr 1
    push_cast
    ring
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Plane)
      (fun x : Plane ↦ f (x + -p)) ξ =
    (Real.fourierChar (inner ℝ (-p) ξ) : ℂ) *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Plane) f ξ at h
  rw [hphase] at h
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Plane)
    (fun x : Plane ↦ f (x - p)) ξ = pointPhase p ξ *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Plane) f ξ
  simpa only [sub_eq_add_neg] using h

noncomputable def cutoffSignal (P : Finset Plane) (M r : ℝ) (x : Plane) : ℂ :=
  (∑ p ∈ P, diskIndicator r (x - p)) -
    ((fun y : Plane ↦ (boxDensity M y : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] diskIndicator r) x

theorem integrable_cutoffSignal (P : Finset Plane) (M r : ℝ) :
    Integrable (cutoffSignal P M r) := by
  apply (integrable_finsetSum P (fun p _ ↦ (integrable_diskIndicator r).comp_sub_right p)).sub
  exact (integrable_boxDensity M).ofReal.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_diskIndicator r)

/-- The Fourier transform of actual cutoff counting minus actual area convolution. -/
theorem fourier_cutoffSignal (P : Finset Plane) (M r : ℝ) (ξ : Plane) :
    (𝓕 (cutoffSignal P M r) : Plane → ℂ) ξ =
      (atomicFourier P ξ - (𝓕 (fun y : Plane ↦ (boxDensity M y : ℂ)) : Plane → ℂ) ξ) *
        (𝓕 (diskIndicator r) : Plane → ℂ) ξ := by
  have hsum := integrable_finsetSum P (fun p _ ↦ (integrable_diskIndicator r).comp_sub_right p)
  have hbg : Integrable (fun y : Plane ↦ (boxDensity M y : ℂ)) := (integrable_boxDensity M).ofReal
  have hconv := hbg.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_diskIndicator r)
  unfold cutoffSignal
  rw [fourier_sub_integrable hsum hconv, fourier_finset_sum P _
    (fun p _ ↦ (integrable_diskIndicator r).comp_sub_right p)]
  simp_rw [fourier_translate]
  rw [Real.fourier_mul_convolution_eq hbg (integrable_diskIndicator r)]
  simp only [atomicFourier, Finset.sum_mul, sub_mul]

end DiskDiscrepancy
