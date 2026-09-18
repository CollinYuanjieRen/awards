import MerLeanExperiment.ExteriorDisk
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Uniform empirical measures on the closed unit disk

This module packages a nonempty finite family of points in the closed unit
disk as a probability measure.  Its main lemmas identify integration against
that measure with the normalized finite sum, including the resolvent kernel
used in the Cauchy-transform argument for Erdős problem 973.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace Erdos973

/-- The uniform probability mass function on `Fin (n + 1)`. -/
noncomputable def uniformFinPMF (n : ℕ) : PMF (Fin (n + 1)) :=
  PMF.uniformOfFintype (Fin (n + 1))

/-- The uniform probability measure on `Fin (n + 1)`. -/
noncomputable def uniformFinProbabilityMeasure (n : ℕ) :
    ProbabilityMeasure (Fin (n + 1)) :=
  ⟨(uniformFinPMF n).toMeasure, inferInstance⟩

/-- The uniform empirical probability measure of a nonempty finite family in
the closed unit disk. -/
noncomputable def empiricalMeasure {n : ℕ} (α : Fin (n + 1) → UnitDisk) :
    ProbabilityMeasure UnitDisk :=
  (uniformFinProbabilityMeasure n).map
    (measurable_of_finite α).aemeasurable

/-- Integration against a uniform empirical probability measure is the
normalized finite sum. -/
theorem integral_empiricalMeasure {n : ℕ} (α : Fin (n + 1) → UnitDisk)
    (f : BoundedContinuousFunction UnitDisk ℂ) :
    ∫ z, f z ∂(empiricalMeasure α : Measure UnitDisk) =
      (((n + 1 : ℕ) : ℝ)⁻¹) • ∑ j, f (α j) := by
  change ∫ z, f z ∂Measure.map α ((uniformFinPMF n).toMeasure) = _
  rw [integral_map_of_stronglyMeasurable (measurable_of_finite α)
    f.continuous.stronglyMeasurable]
  rw [PMF.integral_eq_sum]
  simp only [uniformFinPMF, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    Fintype.card_fin, ENNReal.toReal_natCast]
  rw [Finset.smul_sum]

/-- The empirical Cauchy transform is the normalized finite resolvent sum. -/
theorem integral_resolvent_empiricalMeasure {n : ℕ}
    (α : Fin (n + 1) → UnitDisk) {w : ℂ} (hw : 1 < ‖w‖) :
    ∫ z, (w - (z : ℂ))⁻¹ ∂(empiricalMeasure α : Measure UnitDisk) =
      ((n + 1 : ℂ)⁻¹) * ∑ j, (w - (α j : ℂ))⁻¹ := by
  have hdenom : ∀ z : UnitDisk, w - (z : ℂ) ≠ 0 := by
    intro z hzero
    have hzw : w = (z : ℂ) := sub_eq_zero.mp hzero
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      have hz' := z.property
      rw [Metric.mem_closedBall, dist_zero_right] at hz'
      exact hz'
    rw [hzw] at hw
    exact (not_lt_of_ge hz) hw
  let g : C(UnitDisk, ℂ) :=
    ⟨fun z => (w - (z : ℂ))⁻¹,
      (continuous_const.sub continuous_subtype_val).inv₀ hdenom⟩
  let f : BoundedContinuousFunction UnitDisk ℂ :=
    ContinuousMap.equivBoundedOfCompact UnitDisk ℂ g
  simpa [f, g, Complex.real_smul] using integral_empiricalMeasure α f

end Erdos973
