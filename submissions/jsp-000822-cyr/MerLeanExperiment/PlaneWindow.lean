import MerLeanExperiment.DiskModel
import MerLeanExperiment.WindowWeight
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped FourierTransform

namespace DiskDiscrepancy

/-- Coordinate Fubini with the Euclidean volume convention fixed by the target. -/
theorem integral_plane_product {𝕜 : Type*} [RCLike 𝕜] (f : Fin 2 → ℝ → 𝕜) :
    (∫ x : Plane, ∏ i, f i (x i)) = ∏ i, ∫ t : ℝ, f i t := by
  calc
    _ = ∫ x : Fin 2 → ℝ, ∏ i, f i (x i) :=
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp'
        (fun x : Fin 2 → ℝ ↦ ∏ i, f i (x i))
    _ = _ := integral_fintype_prod_volume_eq_prod f

theorem integrable_plane_product {𝕜 : Type*} [NormedCommRing 𝕜]
    {f : Fin 2 → ℝ → 𝕜} (hf : ∀ i, Integrable (f i)) :
    Integrable (fun x : Plane ↦ ∏ i, f i (x i)) := by
  have h := Integrable.fintype_prod hf
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding |>.mpr h

/-- The tensor product Fourier identity uses the genuine Euclidean inner product. -/
theorem fourier_plane_product (f : Fin 2 → ℝ → ℂ) (x : Plane) :
    𝓕 (fun y : Plane ↦ ∏ i, f i (y i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.inner_apply, smul_eq_mul]
  rw [← integral_plane_product (fun i t ↦
    Complex.exp (↑(-2 * Real.pi * (t * x i)) * Complex.I) * f i t)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two, Fin.prod_univ_two]
  rw [show Complex.exp (↑(-2 * Real.pi * (y 0 * x 0 + y 1 * x 1)) * Complex.I) =
      Complex.exp (↑(-2 * Real.pi * (y 0 * x 0)) * Complex.I) *
      Complex.exp (↑(-2 * Real.pi * (y 1 * x 1)) * Complex.I) by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  ring

noncomputable def planeWindow (a : ℝ) (x : Plane) : ℝ := ∏ i, windowWeight a (x i)
noncomputable def planeKernel (a : ℝ) (x : Plane) : ℝ := ∏ i, sincKernel a (x i)

theorem planeWindow_nonneg {a : ℝ} (ha : 0 < a) (x : Plane) : 0 ≤ planeWindow a x :=
  Finset.prod_nonneg fun i _ ↦ windowWeight_nonneg ha (x i)

theorem planeWindow_le_one {a : ℝ} (ha : 0 < a) (x : Plane) : planeWindow a x ≤ 1 := by
  exact Finset.prod_le_one (fun i _ ↦ windowWeight_nonneg ha (x i))
    (fun i _ ↦ windowWeight_le_one ha (x i))

theorem planeWindow_eq_zero {a : ℝ} {x : Plane} (h : ∃ i, a < |x i|) :
    planeWindow a x = 0 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (windowWeight_eq_zero_of_lt_abs hi)

theorem integrable_planeWindow (a : ℝ) : Integrable (planeWindow a) :=
  integrable_plane_product fun _ ↦ integrable_windowWeight a

theorem planeKernel_nonneg {a : ℝ} (ha : 0 < a) (x : Plane) : 0 ≤ planeKernel a x :=
  Finset.prod_nonneg fun i _ ↦ sincKernel_nonneg ha (x i)

@[simp] theorem planeKernel_zero (a : ℝ) : planeKernel a 0 = a ^ 2 := by
  simp [planeKernel, pow_two]

theorem integrable_planeKernel {a : ℝ} (ha : 0 < a) : Integrable (planeKernel a) :=
  integrable_plane_product fun _ ↦ integrable_sincKernel ha

theorem integral_planeKernel_le_four {a : ℝ} (ha : 0 < a) :
    (∫ x : Plane, planeKernel a x) ≤ 4 := by
  change (∫ x : Plane, ∏ i, sincKernel a (x i)) ≤ 4
  rw [integral_plane_product (fun _ t ↦ sincKernel a t)]
  simp only [Fin.prod_univ_two]
  have h0 : 0 ≤ ∫ t : ℝ, sincKernel a t := integral_nonneg (sincKernel_nonneg ha)
  have h2 := integral_sincKernel_le_two ha
  nlinarith

theorem fourier_planeWindow {a : ℝ} (ha : 0 < a) (x : Plane) :
    𝓕 (fun y : Plane ↦ (planeWindow a y : ℂ)) x = (planeKernel a x : ℂ) := by
  simp only [planeWindow, Complex.ofReal_prod]
  rw [fourier_plane_product (fun _ t ↦ (windowWeight a t : ℂ)) x]
  simp only [fourier_windowWeight ha, planeKernel, Complex.ofReal_prod]

end DiskDiscrepancy
