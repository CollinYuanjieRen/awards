import MerLeanExperiment.FourierNonzero
import MerLeanExperiment.FourierTranslate

/-! Eigenvalues of circle translations belong to the integer character spectrum. -/

namespace Kesten

open AddCircle MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local notation "circleMeasure" =>
  (@AddCircle.haarAddCircle (1 : ℝ) inferInstance :
    @Measure (AddCircle (1 : ℝ))
      (QuotientAddGroup.measurableSpace (AddSubgroup.zmultiples (1 : ℝ))))

/-- Every measurable unit-modulus eigenfunction of a unit-circle translation has an integer
character eigenvalue. -/
theorem spectrum_integer_relation (α β : ℝ) (F : AddCircle (1 : ℝ) → ℂ)
    (hF : AEStronglyMeasurable F circleMeasure)
    (hnorm : ∀ᵐ x ∂circleMeasure, ‖F x‖ = 1)
    (heig : ∀ᵐ x ∂circleMeasure,
      F (x + (α : AddCircle (1 : ℝ))) =
        (↑(toCircle (β : AddCircle (1 : ℝ))) : ℂ) * F x) :
    ∃ k l : ℤ, β = (k : ℝ) * α + (l : ℝ) := by
  obtain ⟨k, hk⟩ := exists_fourierCoeff_ne_zero_of_norm_one F hF hnorm
  have hcoeff :
      fourierCoeff (fun x ↦ F (x + (α : AddCircle (1 : ℝ)))) k =
        fourierCoeff
          (fun x ↦ (↑(toCircle (β : AddCircle (1 : ℝ))) : ℂ) * F x) k :=
    congrFun (fourierCoeff_congr_ae heig) k
  rw [fourierCoeff_translate, fourierCoeff.const_mul] at hcoeff
  have hchar_complex :
      fourier k (α : AddCircle (1 : ℝ)) =
        (↑(toCircle (β : AddCircle (1 : ℝ))) : ℂ) :=
    mul_right_cancel₀ hk hcoeff
  have hchar_circle :
      toCircle (k • (α : AddCircle (1 : ℝ))) =
        toCircle (β : AddCircle (1 : ℝ)) := by
    apply Circle.coe_injective
    simpa only [fourier_apply] using hchar_complex
  have hcircle :
      k • (α : AddCircle (1 : ℝ)) = (β : AddCircle (1 : ℝ)) :=
    AddCircle.injective_toCircle one_ne_zero hchar_circle
  have hzero : ((β - (k : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [← zsmul_eq_mul, coe_sub, coe_zsmul, hcircle, sub_self]
  obtain ⟨l, hl⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero
  refine ⟨k, l, ?_⟩
  norm_num at hl ⊢
  linarith

end Kesten
