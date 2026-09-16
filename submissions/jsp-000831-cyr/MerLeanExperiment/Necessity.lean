import MerLeanExperiment.BirkhoffBridge
import MerLeanExperiment.DenseBound
import MerLeanExperiment.BoundedTransfer
import MerLeanExperiment.Spectrum

/-! Kesten necessity: bounded discrepancy, measurable transfer, and circle spectrum. -/

namespace Kesten

open AddCircle MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local notation "circleMeasure" =>
  (@AddCircle.haarAddCircle (1 : ℝ) inferInstance :
    @Measure (AddCircle (1 : ℝ))
      (QuotientAddGroup.measurableSpace (AddSubgroup.zmultiples (1 : ℝ))))

/-- Bounded discrepancy for an irrational rotation forces the interval length to belong to
`ℤ α + ℤ`. -/
theorem integer_relation_of_bounded_remainder (α u v : ℝ) (hα : Irrational α)
    (huv : u < v) (hb : HasBoundedRemainder α u v) :
    ∃ k l : ℤ, v - u = (k : ℝ) * α + (l : ℝ) := by
  let T : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := fun x ↦ x + α
  let f : AddCircle (1 : ℝ) → ℝ := fun x ↦ intervalIndicator u v x - (v - u)
  obtain ⟨C, hC, hbound⟩ := (hasBoundedRemainder_iff_forall α u v).mp hb
  have hTcont : Continuous T := by fun_prop
  have hTmeas : Measurable T := hTcont.measurable
  have hfmeas : Measurable f := by
    exact (measurable_intervalIndicator u v).sub measurable_const
  have horbit : ∀ n : ℕ,
      |birkhoffSum T f n (α : AddCircle (1 : ℝ))| ≤ C := by
    intro n
    rw [show birkhoffSum T f n (α : AddCircle (1 : ℝ)) =
      (countInIco α u v n : ℝ) - (n : ℝ) * (v - u) by
        exact birkhoffSum_eq_count_discrepancy α u v n]
    exact hbound n
  have haeBound : ∀ᵐ x ∂circleMeasure, ∀ n : ℕ, |birkhoffSum T f n x| ≤ 2 * C := by
    apply ae_birkhoffSum_bound_of_denseRange T f circleMeasure
      (α : AddCircle (1 : ℝ)) C hTcont
    · exact measurePreserving_rotation (α : AddCircle (1 : ℝ))
    · exact denseRange_rotation α hα
    · exact ae_continuousAt_intervalIndicator huv |>.mono fun x hx ↦
        hx.sub continuousAt_const
    · exact horbit
  obtain ⟨h, hhmeas, _, htransfer⟩ :=
    exists_ae_bounded_transfer T f (2 * C) circleMeasure hTmeas hfmeas haeBound
  let F : AddCircle (1 : ℝ) → ℂ := fun x ↦
    (↑(toCircle ((h x : ℝ) : AddCircle (1 : ℝ))) : ℂ)
  have hFmeas : AEStronglyMeasurable F circleMeasure := by
    have hc : Continuous (fun t : ℝ ↦
        (↑(toCircle ((t : ℝ) : AddCircle (1 : ℝ))) : ℂ)) :=
      continuous_subtype_val.comp <|
        continuous_toCircle.comp (AddCircle.continuous_mk' (1 : ℝ))
    exact (hc.measurable.comp hhmeas).aestronglyMeasurable
  have hFnorm : ∀ᵐ x ∂circleMeasure, ‖F x‖ = 1 := by
    filter_upwards [] with x
    exact Circle.norm_coe _
  have hFeig : ∀ᵐ x ∂circleMeasure,
      F (x + (α : AddCircle (1 : ℝ))) =
        (↑(toCircle ((v - u : ℝ) : AddCircle (1 : ℝ))) : ℂ) * F x := by
    filter_upwards [htransfer] with x hx
    have hindicator : ((intervalIndicator u v x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      unfold intervalIndicator
      split <;> simp
    have hcircle :
        ((h (T x) : ℝ) : AddCircle (1 : ℝ)) =
          ((v - u : ℝ) : AddCircle (1 : ℝ)) +
            ((h x : ℝ) : AddCircle (1 : ℝ)) := by
      rw [hx]
      change ((h x - (intervalIndicator u v x - (v - u)) : ℝ) :
          AddCircle (1 : ℝ)) = _
      rw [coe_sub, coe_sub]
      rw [hindicator]
      abel
    change (↑(toCircle ((h (T x) : ℝ) : AddCircle (1 : ℝ))) : ℂ) = _
    rw [hcircle, toCircle_add, Circle.coe_mul]
  exact spectrum_integer_relation α (v - u) F hFmeas hFnorm hFeig

end Kesten
