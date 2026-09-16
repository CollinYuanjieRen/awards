import MerLeanExperiment.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Perfect

/-! Measurability and almost-everywhere continuity of the interval indicator. -/

namespace Kesten

open AddCircle MeasureTheory Set

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance : Nontrivial (AddCircle (1 : ℝ)) :=
  ⟨⟨0, ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), by
    intro h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h.symm
    norm_num [zsmul_eq_mul] at hn
    have hnpos_real : (0 : ℝ) < (n : ℝ) := by rw [hn]; norm_num
    have hnlt_real : (n : ℝ) < 1 := by rw [hn]; norm_num
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hnpos_real
    have hnlt : n < (1 : ℤ) := by exact_mod_cast hnlt_real
    omega⟩⟩

local notation "circleMeasure" =>
  (@AddCircle.haarAddCircle (1 : ℝ) inferInstance :
    @Measure (AddCircle (1 : ℝ))
      (QuotientAddGroup.measurableSpace (AddSubgroup.zmultiples (1 : ℝ))))

/-- On a real representative, the circle interval indicator is the corresponding fractional-part
indicator. -/
theorem intervalIndicator_coe (u v x : ℝ) :
    intervalIndicator u v (x : AddCircle (1 : ℝ)) =
      if u ≤ Int.fract x ∧ Int.fract x < v then 1 else 0 := by
  simp [intervalIndicator, AddCircle.coe_equivIco_mk_apply]

/-- The interval indicator on the unit additive circle is measurable. -/
theorem measurable_intervalIndicator (u v : ℝ) : Measurable (intervalIndicator u v) := by
  let r : AddCircle (1 : ℝ) → ℝ := fun x ↦ (AddCircle.equivIco 1 0 x : ℝ)
  have hr : Measurable r :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  have hi : Measurable ((Ico u v).indicator fun _ : ℝ ↦ (1 : ℝ)) :=
    measurable_const.indicator measurableSet_Ico
  have heq : intervalIndicator u v = ((Ico u v).indicator fun _ : ℝ ↦ (1 : ℝ)) ∘ r := by
    funext x
    simp [intervalIndicator, r, Set.indicator, mem_Ico]
  rw [heq]
  exact hi.comp hr

/-- The interval indicator is continuous almost everywhere when its endpoints are ordered. -/
theorem ae_continuousAt_intervalIndicator {u v : ℝ} (huv : u < v) :
    ∀ᵐ x ∂circleMeasure, ContinuousAt (intervalIndicator u v) x := by
  filter_upwards [Measure.ae_ne circleMeasure (0 : AddCircle (1 : ℝ)),
    Measure.ae_ne circleMeasure (u : AddCircle (1 : ℝ)),
    Measure.ae_ne circleMeasure (v : AddCircle (1 : ℝ))] with x hx0 hxu hxv
  let r : AddCircle (1 : ℝ) → ℝ := fun y ↦ (AddCircle.equivIco 1 0 y : ℝ)
  have hr : ContinuousAt r x :=
    continuousAt_subtype_val.comp (AddCircle.continuousAt_equivIco 1 0 hx0)
  have hru : r x ≠ u := by
    intro h
    apply hxu
    calc
      x = ((AddCircle.equivIco 1 0 x : ℝ) : AddCircle (1 : ℝ)) :=
        AddCircle.coe_equivIco.symm
      _ = (u : AddCircle (1 : ℝ)) := congrArg (fun z : ℝ ↦ (z : AddCircle (1 : ℝ))) h
  have hrv : r x ≠ v := by
    intro h
    apply hxv
    calc
      x = ((AddCircle.equivIco 1 0 x : ℝ) : AddCircle (1 : ℝ)) :=
        AddCircle.coe_equivIco.symm
      _ = (v : AddCircle (1 : ℝ)) := congrArg (fun z : ℝ ↦ (z : AddCircle (1 : ℝ))) h
  have hfrontier : r x ∉ frontier (Ico u v) := by
    simp [frontier_Ico huv, hru, hrv]
  have hi : ContinuousAt ((Ico u v).indicator fun _ : ℝ ↦ (1 : ℝ)) (r x) :=
    continuousOn_const.continuousAt_indicator hfrontier
  have heq : intervalIndicator u v = ((Ico u v).indicator fun _ : ℝ ↦ (1 : ℝ)) ∘ r := by
    funext y
    simp [intervalIndicator, r, Set.indicator, mem_Ico]
  rw [heq]
  exact hi.comp hr

end Kesten
