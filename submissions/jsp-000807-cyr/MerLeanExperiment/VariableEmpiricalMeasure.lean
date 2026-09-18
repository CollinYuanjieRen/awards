import MerLeanExperiment.CauchyTransformGeneral
import MerLeanExperiment.EmpiricalMeasure

/-!
# Empirical measures for rows of arbitrary positive size

This file removes the `n + 1` indexing convention from the empirical-measure
interface.  A proof that a row size is positive supplies the nonempty instance
needed for the uniform probability mass function on `Fin m`.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace Erdos973

/-- The uniform probability mass function on `Fin m`, when `m` is positive. -/
noncomputable def uniformFinPMFOfPositive (m : ℕ) (hm : 0 < m) : PMF (Fin m) := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  exact PMF.uniformOfFintype (Fin m)

/-- The uniform probability measure on `Fin m`, when `m` is positive. -/
noncomputable def uniformFinProbabilityMeasureOfPositive (m : ℕ) (hm : 0 < m) :
    ProbabilityMeasure (Fin m) :=
  ⟨(uniformFinPMFOfPositive m hm).toMeasure, inferInstance⟩

/-- The uniform empirical measure of an arbitrary nonempty finite row. -/
noncomputable def variableEmpiricalMeasure {m : ℕ} (hm : 0 < m)
    (α : Fin m → UnitDisk) : ProbabilityMeasure UnitDisk :=
  (uniformFinProbabilityMeasureOfPositive m hm).map
    (measurable_of_finite α).aemeasurable

/-- Integration against an arbitrary positive-size empirical measure is the
normalized finite sum. -/
theorem integral_variableEmpiricalMeasure {m : ℕ} (hm : 0 < m)
    (α : Fin m → UnitDisk) (f : BoundedContinuousFunction UnitDisk ℂ) :
    ∫ z, f z ∂(variableEmpiricalMeasure hm α : Measure UnitDisk) =
      ((m : ℝ)⁻¹) • ∑ j, f (α j) := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  change ∫ z, f z ∂Measure.map α ((uniformFinPMFOfPositive m hm).toMeasure) = _
  rw [integral_map_of_stronglyMeasurable (measurable_of_finite α)
    f.continuous.stronglyMeasurable]
  rw [PMF.integral_eq_sum]
  simp only [uniformFinPMFOfPositive, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, Fintype.card_fin, ENNReal.toReal_natCast]
  rw [Finset.smul_sum]

/-- The Cauchy transform of an arbitrary positive-size empirical measure is
its normalized finite resolvent sum. -/
theorem cauchyTransform_variableEmpiricalMeasure_eq_finite {m : ℕ}
    (hm : 0 < m) (α : Fin m → UnitDisk) {w : ℂ} (hw : w ∈ exterior) :
    cauchyTransform (variableEmpiricalMeasure hm α) w =
      ((m : ℂ)⁻¹) * ∑ j, (w - (α j : ℂ))⁻¹ := by
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
  simpa [cauchyTransform, f, g, Complex.real_smul] using
    integral_variableEmpiricalMeasure hm α f

/-- The arbitrary-size empirical Cauchy transform is holomorphic on the
exterior disk. -/
theorem differentiableOn_cauchyTransform_variableEmpiricalMeasure {m : ℕ}
    (hm : 0 < m) (α : Fin m → UnitDisk) :
    DifferentiableOn ℂ (cauchyTransform (variableEmpiricalMeasure hm α)) exterior := by
  have hterm : ∀ j : Fin m,
      DifferentiableOn ℂ (fun w : ℂ => (w - (α j : ℂ))⁻¹) exterior := by
    intro j
    apply (differentiableOn_id.sub
      (differentiableOn_const (c := (α j : ℂ)))).inv
    intro w hw hzero
    have heq : w = (α j : ℂ) := sub_eq_zero.mp hzero
    have hz : ‖(α j : ℂ)‖ ≤ 1 := by
      have hz' := (α j).property
      change dist (α j : ℂ) 0 ≤ 1 at hz'
      simpa [dist_zero_right] using hz'
    rw [heq] at hw
    exact (not_lt_of_ge hz) hw
  have hfinite : DifferentiableOn ℂ
      (fun w : ℂ => ((m : ℂ)⁻¹) * ∑ j, (w - (α j : ℂ))⁻¹) exterior := by
    apply (differentiableOn_const (c := ((m : ℂ)⁻¹))).mul
    exact DifferentiableOn.fun_sum (u := Finset.univ) fun j _ => hterm j
  exact hfinite.congr fun w hw =>
    cauchyTransform_variableEmpiricalMeasure_eq_finite hm α hw

/-- Sequence-level arbitrary-row-size adapter for
`constant_limit_cauchyTransform_eq_zero_general`. -/
theorem constant_limit_variableEmpiricalCauchyTransform_eq_zero
    (size : ℕ → ℕ) (hsize : ∀ n, 0 < size n)
    (α : ∀ n, Fin (size n) → UnitDisk) (V : Set ℂ) (c : ℂ)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVext : V ⊆ exterior)
    (hconv : ∀ w ∈ V, Tendsto
      (fun n => ((size n : ℂ)⁻¹) * ∑ j, (w - (α n j : ℂ))⁻¹)
      atTop (𝓝 c)) :
    c = 0 := by
  let μ : ℕ → ProbabilityMeasure UnitDisk :=
    fun n => variableEmpiricalMeasure (hsize n) (α n)
  apply constant_limit_cauchyTransform_eq_zero_general μ V c hVopen hVne hVext
  · intro n
    exact differentiableOn_cauchyTransform_variableEmpiricalMeasure
      (hsize n) (α n)
  · intro w hw
    apply (hconv w hw).congr'
    filter_upwards with n
    exact (cauchyTransform_variableEmpiricalMeasure_eq_finite
      (hsize n) (α n) (hVext hw)).symm

end Erdos973
