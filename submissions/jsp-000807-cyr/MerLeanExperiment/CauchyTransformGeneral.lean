import MerLeanExperiment.CauchyTransformIdentity

/-! A cardinality-independent form of the Cauchy-transform obstruction. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos973

/-- Lemma 4.1 for an arbitrary sequence of probability measures.  This is the
interface used by a counterexample subsequence whose row sizes need not equal
`n+1`. -/
theorem constant_limit_cauchyTransform_eq_zero_general
    (μ : ℕ → ProbabilityMeasure UnitDisk) (V : Set ℂ) (c : ℂ)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVext : V ⊆ exterior)
    (hdiff : ∀ n, DifferentiableOn ℂ (cauchyTransform (μ n)) exterior)
    (hconv : ∀ w ∈ V,
      Tendsto (fun n => cauchyTransform (μ n) w) atTop (𝓝 c)) :
    c = 0 := by
  obtain ⟨ν, φ, hφ, hweak, _⟩ := exists_cauchyTransform_tendsto_subseq μ
  have hlu : TendstoLocallyUniformlyOn
      (fun n => cauchyTransform ((μ ∘ φ) n)) (cauchyTransform ν) atTop exterior :=
    cauchyTransform_tendstoLocallyUniformlyOn_of_weak hweak
  have hdiff' : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (cauchyTransform ((μ ∘ φ) n)) exterior := by
    filter_upwards with n
    exact hdiff (φ n)
  have hlimitDiff : DifferentiableOn ℂ (cauchyTransform ν) exterior :=
    hlu.differentiableOn hdiff' isOpen_exterior
  have hlimitAnalytic : AnalyticOnNhd ℂ (cauchyTransform ν) exterior :=
    hlimitDiff.analyticOnNhd isOpen_exterior
  have hconstV : Set.EqOn (cauchyTransform ν) (fun _ => c) V := by
    intro w hw
    have hlim := hlu.tendsto_at (hVext hw)
    have hcsub := (hconv w hw).comp hφ.tendsto_atTop
    have hlim' : Tendsto (fun n => cauchyTransform (μ (φ n)) w)
        atTop (𝓝 (cauchyTransform ν w)) := by
      simpa [Function.comp_apply] using hlim
    exact tendsto_nhds_unique hlim' hcsub
  obtain ⟨w₀, hw₀⟩ := hVne
  have heventually : cauchyTransform ν =ᶠ[𝓝 w₀] fun _ => c :=
    mem_of_superset (hVopen.mem_nhds hw₀) hconstV
  have hglobal : Set.EqOn (cauchyTransform ν) (fun _ => c) exterior :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hlimitAnalytic analyticOnNhd_const isPreconnected_exterior
      (hVext hw₀) heventually
  exact constant_cauchyTransform_eq_zero ν c fun w hw => hglobal hw

end Erdos973
