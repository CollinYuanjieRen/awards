import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.LpSpace

open MeasureTheory
open scoped ComplexConjugate ContDiff FourierTransform

namespace DiskDiscrepancy

/-- A local name for the two-dimensional Euclidean space used by the Fourier bridge. -/
private abbrev FourierPlane := EuclideanSpace ℝ (Fin 2)

set_option maxHeartbeats 2000000 in
/-- The `L²` Fourier transform of an integrable function agrees almost everywhere with its
classical Fourier integral. -/
theorem fourier_toLp_ae_eq_general {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {f : E → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    (fun x ↦ (𝓕 (h2.toLp f) : Lp (α := E) ℂ 2) x) =ᵐ[volume] (𝓕 f : E → ℂ) := by
  let u : Lp (α := E) ℂ 2 := h2.toLp f
  let v : Lp (α := E) ℂ 2 := 𝓕 u
  have hv : LocallyIntegrable (fun x ↦ v x) volume :=
    (Lp.memLp v).locallyIntegrable (by norm_num)
  have hF_cont : Continuous (𝓕 f : E → ℂ) := by
    have heq : (𝓕 f : E → ℂ) =
        VectorFourier.fourierIntegral Real.fourierChar volume
          (innerₗ E) f :=
      funext (Real.fourier_eq f)
    rw [heq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous₂ h1
  change (fun x ↦ v x) =ᵐ[volume] (𝓕 f : E → ℂ)
  apply ae_eq_of_integral_contDiff_smul_eq hv hF_cont.locallyIntegrable
  intro g hg_diff hg_cpt
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg_cpt.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg_diff
  let ψ : SchwartzMap E ℂ := hg₁.toSchwartzMap hg₂
  have hu_ae : (fun x ↦ u x) =ᵐ[volume] f := h2.coeFn_toLp
  calc
    (∫ x, g x • v x) = ∫ x, ψ x • v x := by simp [ψ]
    _ = (v : TemperedDistribution E ℂ) ψ := by
      rw [Lp.toTemperedDistribution_apply]
    _ = (𝓕 (u : TemperedDistribution E ℂ)) ψ := by
      rw [Lp.fourier_toTemperedDistribution_eq]
    _ = (u : TemperedDistribution E ℂ) (𝓕 ψ) := by
      rw [TemperedDistribution.fourier_apply]
    _ = ∫ x, (𝓕 ψ) x • u x := by
      rw [Lp.toTemperedDistribution_apply]
    _ = ∫ x, (𝓕 ψ) x * f x := by
      apply integral_congr_ae
      filter_upwards [hu_ae] with x hx
      simp [hx, mul_comm]
    _ = ∫ x, ψ x * (𝓕 f : E → ℂ) x := by
      have hpair :=
        VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar
          (μ := volume) (ν := volume) (L := innerₗ E)
          (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous₂ h1 ψ.integrable
      have hf_eq : (𝓕 f : E → ℂ) =
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) f :=
        funext (Real.fourier_eq f)
      have hψ_eq : (𝓕 (ψ : E → ℂ) : E → ℂ) =
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ E) ψ :=
        funext (Real.fourier_eq (ψ : E → ℂ))
      rw [hf_eq, SchwartzMap.fourier_coe, hψ_eq]
      simpa only [flip_innerₗ, smul_eq_mul, mul_comm] using hpair.symm
    _ = ∫ x, g x • (𝓕 f : E → ℂ) x := by simp [ψ]

/-- On the Euclidean plane, the `L²` Fourier transform agrees almost everywhere with the
classical Fourier integral. -/
theorem fourier_toLp_ae_eq {f : FourierPlane → ℂ} (h1 : Integrable f) (h2 : MemLp f 2) :
    (fun x ↦ (𝓕 (h2.toLp f) : Lp (α := FourierPlane) ℂ 2) x) =ᵐ[volume]
      (𝓕 f : FourierPlane → ℂ) := by
  exact fourier_toLp_ae_eq_general h1 h2

/-- The classical Fourier integral of an integrable `L²` function on the plane is in `L²`. -/
theorem memLp_fourier_of_integrable_memLp_two {f : FourierPlane → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) : MemLp (𝓕 f : FourierPlane → ℂ) 2 := by
  let v : Lp (α := FourierPlane) ℂ 2 := 𝓕 (h2.toLp f)
  exact (memLp_congr_ae (μ := volume) (fourier_toLp_ae_eq h1 h2)).mp
    (Lp.memLp v)

/-- Classical Plancherel identity for integrable `L²` functions on the Euclidean plane. -/
theorem integral_norm_sq_fourier_of_integrable_memLp_two {f : FourierPlane → ℂ}
    (h1 : Integrable f) (h2 : MemLp f 2) :
    (∫ ξ, ‖(𝓕 f : FourierPlane → ℂ) ξ‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  let u : Lp (α := FourierPlane) ℂ 2 := h2.toLp f
  let v : Lp (α := FourierPlane) ℂ 2 := 𝓕 u
  have hv_ae : (fun x ↦ v x) =ᵐ[volume] (𝓕 f : FourierPlane → ℂ) :=
    fourier_toLp_ae_eq h1 h2
  have hu_ae : (fun x ↦ u x) =ᵐ[volume] f := h2.coeFn_toLp
  have hv_re : (∫ x, ‖v x‖ ^ 2) =
      Complex.re (∫ x, @inner ℂ ℂ _ (v x) (v x)) := by
    calc
      (∫ x, ‖v x‖ ^ 2) = ∫ x, Complex.re (@inner ℂ ℂ _ (v x) (v x)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [inner_self_eq_norm_sq_to_K]
        change ‖v x‖ ^ 2 = Complex.re ((‖v x‖ : ℂ) ^ 2)
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
      _ = Complex.re (∫ x, @inner ℂ ℂ _ (v x) (v x)) :=
        integral_re (𝕜 := ℂ) (L2.integrable_inner v v)
  have hu_re : (∫ x, ‖u x‖ ^ 2) =
      Complex.re (∫ x, @inner ℂ ℂ _ (u x) (u x)) := by
    calc
      (∫ x, ‖u x‖ ^ 2) = ∫ x, Complex.re (@inner ℂ ℂ _ (u x) (u x)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [inner_self_eq_norm_sq_to_K]
        change ‖u x‖ ^ 2 = Complex.re ((‖u x‖ : ℂ) ^ 2)
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
      _ = Complex.re (∫ x, @inner ℂ ℂ _ (u x) (u x)) :=
        integral_re (𝕜 := ℂ) (L2.integrable_inner u u)
  calc
    (∫ ξ, ‖(𝓕 f : FourierPlane → ℂ) ξ‖ ^ 2) = ∫ ξ, ‖v ξ‖ ^ 2 :=
      integral_congr_ae (hv_ae.symm.fun_comp fun z : ℂ ↦ ‖z‖ ^ 2)
    _ = ∫ x, ‖u x‖ ^ 2 := by
      rw [hv_re, hu_re, ← L2.inner_def, ← L2.inner_def]
      simpa only [v] using congr_arg Complex.re (Lp.inner_fourier_eq u u)
    _ = ∫ x, ‖f x‖ ^ 2 :=
      integral_congr_ae (hu_ae.fun_comp fun z : ℂ ↦ ‖z‖ ^ 2)

end DiskDiscrepancy
