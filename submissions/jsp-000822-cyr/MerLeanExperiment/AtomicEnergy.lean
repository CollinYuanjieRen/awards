import MerLeanExperiment.PlaneWindow

open MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace DiskDiscrepancy

noncomputable def pointPhase (p ξ : Plane) : ℂ :=
  Complex.exp (↑(-2 * Real.pi * inner ℝ ξ p) * Complex.I)

@[simp] theorem norm_pointPhase (p ξ : Plane) : ‖pointPhase p ξ‖ = 1 := by
  simp [pointPhase, Complex.norm_exp]

theorem continuous_pointPhase (p : Plane) : Continuous (pointPhase p) := by
  unfold pointPhase
  fun_prop

theorem pointPhase_sub (p q ξ : Plane) :
    pointPhase (p - q) ξ = pointPhase p ξ * conj (pointPhase q ξ) := by
  unfold pointPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_right, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem pointPhase_add (p q ξ : Plane) :
    pointPhase (p + q) ξ = pointPhase p ξ * pointPhase q ξ := by
  unfold pointPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_add_right]
  push_cast
  ring

@[simp] theorem pointPhase_neg (p ξ : Plane) :
    pointPhase (-p) ξ = conj (pointPhase p ξ) := by
  simpa [pointPhase] using pointPhase_sub 0 p ξ

theorem integrable_weighted_pointPhase (a : ℝ) (p : Plane) :
    Integrable (fun ξ : Plane ↦ (planeWindow a ξ : ℂ) * pointPhase p ξ) := by
  apply (integrable_planeWindow a).ofReal.mul_bdd (c := 1)
    (continuous_pointPhase p).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ ↦ (norm_pointPhase p ξ).le

theorem integral_weighted_pointPhase {a : ℝ} (ha : 0 < a) (p : Plane) :
    (∫ ξ : Plane, (planeWindow a ξ : ℂ) * pointPhase p ξ) = (planeKernel a p : ℂ) := by
  have h := fourier_planeWindow ha p
  rw [Real.fourier_eq'] at h
  simpa only [pointPhase, smul_eq_mul, mul_comm] using h

noncomputable def atomicFourier (P : Finset Plane) (ξ : Plane) : ℂ :=
  ∑ p ∈ P, pointPhase p ξ

theorem atomicFourier_norm_sq (P : Finset Plane) (ξ : Plane) :
    (‖atomicFourier P ξ‖ ^ 2 : ℂ) = ∑ p ∈ P, ∑ q ∈ P, pointPhase (p - q) ξ := by
  rw [← Complex.mul_conj']
  simp only [atomicFourier, map_sum, Finset.sum_mul, Finset.mul_sum, pointPhase_sub]
  exact Finset.sum_comm

theorem integral_weighted_atomic_norm_sq {a : ℝ} (ha : 0 < a) (P : Finset Plane) :
    (∫ ξ : Plane, planeWindow a ξ * ‖atomicFourier P ξ‖ ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P, planeKernel a (p - q) := by
  have hfun (ξ : Plane) :
      ((planeWindow a ξ * ‖atomicFourier P ξ‖ ^ 2 : ℝ) : ℂ) =
        ∑ p ∈ P, ∑ q ∈ P, (planeWindow a ξ : ℂ) * pointPhase (p - q) ξ := by
    push_cast
    rw [atomicFourier_norm_sq]
    simp only [Finset.mul_sum]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hfun]
  rw [integral_finsetSum P (fun p _ ↦
    integrable_finsetSum P (fun q _ ↦ integrable_weighted_pointPhase a (p - q)))]
  have hinner (p : Plane) :
      (∫ ξ : Plane, ∑ q ∈ P, (planeWindow a ξ : ℂ) * pointPhase (p - q) ξ) =
        ∑ q ∈ P, (planeKernel a (p - q) : ℂ) := by
    rw [integral_finsetSum P (fun q _ ↦ integrable_weighted_pointPhase a (p - q))]
    simp only [integral_weighted_pointPhase ha]
  simp only [hinner, Complex.ofReal_sum]

theorem atomic_window_energy_lower {a : ℝ} (ha : 0 < a) (P : Finset Plane) :
    a ^ 2 * P.card ≤ ∫ ξ : Plane, planeWindow a ξ * ‖atomicFourier P ξ‖ ^ 2 := by
  rw [integral_weighted_atomic_norm_sq ha]
  calc
    _ = ∑ p ∈ P, a ^ 2 := by simp [mul_comm]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, planeKernel a (p - q) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        a ^ 2 = planeKernel a (p - p) := by simp
        _ ≤ ∑ q ∈ P, planeKernel a (p - q) :=
          Finset.single_le_sum (fun q _ ↦ planeKernel_nonneg ha (p - q)) hp

end DiskDiscrepancy
