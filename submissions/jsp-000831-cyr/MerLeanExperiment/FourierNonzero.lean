import Mathlib.Analysis.Fourier.AddCircle

/-! A nonzero L² function on the circle has a nonzero Fourier coefficient. -/

namespace Kesten

open MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local notation "circleMeasure" =>
  (@AddCircle.haarAddCircle (1 : ℝ) inferInstance :
    @Measure (AddCircle (1 : ℝ))
      (QuotientAddGroup.measurableSpace (AddSubgroup.zmultiples (1 : ℝ))))

/-- A measurable circle function of norm one almost everywhere has a nonzero Fourier
coefficient. -/
theorem exists_fourierCoeff_ne_zero_of_norm_one
    (F : AddCircle (1 : ℝ) → ℂ)
    (hF : AEStronglyMeasurable F circleMeasure)
    (hnorm : ∀ᵐ x ∂circleMeasure, ‖F x‖ = 1) :
    ∃ k : ℤ, fourierCoeff F k ≠ 0 := by
  have hF2 : MemLp F 2 circleMeasure :=
    MemLp.of_bound (α := AddCircle (1 : ℝ)) (E := ℂ)
      (m0 := QuotientAddGroup.measurableSpace (AddSubgroup.zmultiples (1 : ℝ)))
      (μ := circleMeasure) (p := 2) hF 1 <| hnorm.mono fun _ hx ↦ hx.le
  by_contra h
  push Not at h
  have hre : (@fourierBasis (1 : ℝ) inferInstance).repr hF2.toLp = 0 := by
    ext k
    have hk : fourierCoeff hF2.toLp k = 0 := by
      rw [fourierCoeff_congr_ae hF2.coeFn_toLp]
      exact h k
    simpa [fourierBasis_repr] using hk
  have hzero : hF2.toLp = 0 := by
    apply fourierBasis.repr.injective
    simpa using hre
  have hzero_ae : F =ᵐ[circleMeasure] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hF2.coeFn_toLp] with x hx
    simpa [hzero] using hx.symm
  have hbad : ∀ᵐ x ∂circleMeasure, False := by
    filter_upwards [hnorm, hzero_ae] with x hxnorm hxzero
    simp [hxzero] at hxnorm
  exact hbad.exists.choose_spec

end Kesten
