import MerLeanExperiment.ExteriorDisk
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Compactness for Cauchy transforms on the exterior disk

This file isolates the measure-theoretic core of Lemma 4.1 in the
Luo--Yang--Zhu argument.  A sequence of probability measures on the closed
unit disk has a weakly convergent subsequence, and weak convergence gives
pointwise convergence of its Cauchy transforms at every point outside the
disk.
-/

open Filter MeasureTheory Metric Set
open scoped Topology

namespace Erdos973

/-- The Cauchy transform of a probability measure on the closed unit disk. -/
noncomputable def cauchyTransform (ν : ProbabilityMeasure UnitDisk) (w : ℂ) : ℂ :=
  ∫ z, (w - (z : ℂ))⁻¹ ∂(ν : Measure UnitDisk)

/-- The resolvent kernel on the compact unit disk, bundled as a continuous
map.  The exterior hypothesis ensures that its denominator never vanishes. -/
noncomputable def cauchyKernel (w : ℂ) (hw : 1 < ‖w‖) : C(UnitDisk, ℂ) where
  toFun z := (w - (z : ℂ))⁻¹
  continuous_toFun := by
    apply Continuous.inv₀ (continuous_const.sub continuous_subtype_val)
    intro z
    apply sub_ne_zero.mpr
    intro hwz
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      have hz' := z.property
      change dist (z : ℂ) 0 ≤ 1 at hz'
      simpa [dist_zero_right] using hz'
    change w = (z : ℂ) at hwz
    rw [hwz] at hw
    exact (not_lt_of_ge hz) hw

/-- The same kernel in the bounded-continuous-function API used to
characterize weak convergence of probability measures. -/
noncomputable def boundedCauchyKernel (w : ℂ) (hw : 1 < ‖w‖) :
    BoundedContinuousFunction UnitDisk ℂ :=
  ContinuousMap.equivBoundedOfCompact UnitDisk ℂ (cauchyKernel w hw)

@[simp] theorem boundedCauchyKernel_apply (w : ℂ) (hw : 1 < ‖w‖) (z : UnitDisk) :
    boundedCauchyKernel w hw z = (w - (z : ℂ))⁻¹ :=
  rfl

/-- The elementary separation estimate for the resolvent kernel. -/
theorem norm_cauchyKernel_le (w : ℂ) (hw : 1 < ‖w‖) (z : UnitDisk) :
    ‖(w - (z : ℂ))⁻¹‖ ≤ (‖w‖ - 1)⁻¹ := by
  have hz : ‖(z : ℂ)‖ ≤ 1 := by
    have hz' := z.property
    change dist (z : ℂ) 0 ≤ 1 at hz'
    simpa [dist_zero_right] using hz'
  have hsep : ‖w‖ - 1 ≤ ‖w - (z : ℂ)‖ := by
    have hrev := norm_sub_norm_le w (z : ℂ)
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hsep

/-- A probability Cauchy transform obeys the sharp elementary bound coming
from the distance between `w` and the closed unit disk. -/
theorem norm_cauchyTransform_le (ν : ProbabilityMeasure UnitDisk)
    (w : ℂ) (hw : 1 < ‖w‖) :
    ‖cauchyTransform ν w‖ ≤ (‖w‖ - 1)⁻¹ := by
  simpa only [cauchyTransform, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := (ν : Measure UnitDisk))
      (ae_of_all _ (norm_cauchyKernel_le w hw)))

/-- Weak convergence on the compact disk implies pointwise convergence of
Cauchy transforms throughout the exterior of the disk. -/
theorem cauchyTransform_tendsto_of_weak
    {μ : ℕ → ProbabilityMeasure UnitDisk} {ν : ProbabilityMeasure UnitDisk}
    (hμ : Tendsto μ atTop (𝓝 ν)) (w : ℂ) (hw : 1 < ‖w‖) :
    Tendsto (fun n ↦ cauchyTransform (μ n) w) atTop
      (𝓝 (cauchyTransform ν w)) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hμ
      (boundedCauchyKernel w hw)
  simpa only [cauchyTransform, boundedCauchyKernel_apply] using h

/-- Every sequence of probability measures on the closed unit disk has a
strictly monotone subsequence along which all exterior Cauchy transforms
converge pointwise to the transform of one limiting probability measure. -/
theorem exists_cauchyTransform_tendsto_subseq
    (μ : ℕ → ProbabilityMeasure UnitDisk) :
    ∃ (ν : ProbabilityMeasure UnitDisk) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      ∀ w : ℂ, 1 < ‖w‖ →
        Tendsto (fun n ↦ cauchyTransform (μ (φ n)) w) atTop
          (𝓝 (cauchyTransform ν w)) := by
  obtain ⟨ν, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq μ
  refine ⟨ν, φ, hφ, hμ, ?_⟩
  intro w hw
  simpa only [Function.comp_apply] using
    cauchyTransform_tendsto_of_weak hμ w hw

/-- Along the positive real ray, every probability Cauchy transform tends to
zero at infinity. -/
theorem cauchyTransform_tendsto_zero_atTop (ν : ProbabilityMeasure UnitDisk) :
    Tendsto (fun r : ℝ ↦ cauchyTransform ν (r : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have hw : 1 < ‖(r : ℂ)‖ := by
      simpa [Complex.norm_real, abs_of_pos (lt_trans zero_lt_one hr)] using hr
    simpa [Complex.norm_real, abs_of_pos (lt_trans zero_lt_one hr)] using
      norm_cauchyTransform_le ν (r : ℂ) hw
  · apply tendsto_inv_atTop_zero.comp
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)

/-- Consequently, a Cauchy transform which is constant throughout the
exterior disk has constant value zero.  In the full paper argument, the
identity theorem is what upgrades constancy on a nonempty open subset to this
global exterior hypothesis. -/
theorem constant_cauchyTransform_eq_zero
    (ν : ProbabilityMeasure UnitDisk) (c : ℂ)
    (hconst : ∀ w : ℂ, 1 < ‖w‖ → cauchyTransform ν w = c) :
    c = 0 := by
  have heventually :
      (fun r : ℝ ↦ cauchyTransform ν (r : ℂ)) =ᶠ[atTop] fun _ ↦ c := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    apply hconst
    simpa [Complex.norm_real, abs_of_pos (lt_trans zero_lt_one hr)] using hr
  have hc : Tendsto (fun _ : ℝ ↦ c) atTop (𝓝 0) :=
    (cauchyTransform_tendsto_zero_atTop ν).congr' heventually
  exact tendsto_nhds_unique (by simp) hc

end Erdos973

#print axioms Erdos973.exists_cauchyTransform_tendsto_subseq
#print axioms Erdos973.norm_cauchyTransform_le
#print axioms Erdos973.constant_cauchyTransform_eq_zero
