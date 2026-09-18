import MerLeanExperiment.EmpiricalMeasure
import MerLeanExperiment.CauchyTransformRigidity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# The identity-theorem step for empirical Cauchy transforms

This file completes the topological and complex-analytic bridge in Lemma 4.1:
weak compactness supplies a pointwise convergent subsequence, equicontinuity
upgrades it to locally uniform convergence on the exterior disk, and the
identity theorem forces a locally constant limit to be globally constant.
-/

open Filter MeasureTheory Metric Set
open scoped Topology

namespace Erdos973

/-- The exterior of the closed unit disk. -/
def exterior : Set ℂ := {w | 1 < ‖w‖}

theorem mem_exterior {w : ℂ} : w ∈ exterior ↔ 1 < ‖w‖ := Iff.rfl

theorem isOpen_exterior : IsOpen exterior := by
  exact isOpen_lt continuous_const continuous_norm

theorem exterior_nonempty : exterior.Nonempty := by
  refine ⟨(2 : ℂ), ?_⟩
  norm_num [exterior, Complex.norm_real]

/-- The exterior disk is preconnected.  It is the continuous image of the
product of the positive radial interval and the unit circle. -/
theorem isPreconnected_exterior : IsPreconnected exterior := by
  let S : Set (ℝ × ℂ) := Ioi (1 : ℝ) ×ˢ sphere (0 : ℂ) 1
  let f : ℝ × ℂ → ℂ := fun p ↦ (p.1 : ℂ) * p.2
  have hcircle : IsPathConnected (sphere (0 : ℂ) 1) :=
    isPathConnected_sphere
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 0 (by norm_num)
  have hS : IsPreconnected S :=
    isPreconnected_Ioi.prod hcircle.isConnected.2
  have hf : ContinuousOn f S := by
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd |>.continuousOn
  have himage : f '' S = exterior := by
    apply Set.Subset.antisymm
    · rintro w ⟨p, hp, rfl⟩
      rcases p with ⟨r, u⟩
      rcases hp with ⟨hr, hu⟩
      change 1 < r at hr
      have hu_norm : ‖u‖ = 1 := by
        simpa [mem_sphere_zero_iff_norm] using hu
      simp only [f, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one hr), hu_norm, mul_one, exterior, mem_ofPred_eq]
      exact hr
    · intro w hw
      have hw_norm : 0 < ‖w‖ := lt_trans zero_lt_one hw
      let u : ℂ := (‖w‖ : ℂ)⁻¹ * w
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        simp [u, norm_inv, Complex.norm_real, hw_norm.ne']
      refine ⟨(‖w‖, u), ⟨hw, hu⟩, ?_⟩
      simp [f, u, hw_norm.ne']
  rw [← himage]
  exact hS.image f hf

/-- The empirical Cauchy transform attached to row `n` of a triangular
array in the unit disk. -/
noncomputable def empiricalCauchyTransform
    (α : ∀ n, Fin (n + 1) → UnitDisk) (n : ℕ) (w : ℂ) : ℂ :=
  cauchyTransform (empiricalMeasure (α n)) w

/-- The explicit normalized finite resolvent sum for a row of the triangular
array. -/
noncomputable def finiteCauchyTransform
    (α : ∀ n, Fin (n + 1) → UnitDisk) (n : ℕ) (w : ℂ) : ℂ :=
  ((n + 1 : ℂ)⁻¹) * ∑ j, (w - (α n j : ℂ))⁻¹

theorem empiricalCauchyTransform_eq_finite
    (α : ∀ n, Fin (n + 1) → UnitDisk) (n : ℕ) {w : ℂ} (hw : w ∈ exterior) :
    empiricalCauchyTransform α n w = finiteCauchyTransform α n w := by
  exact integral_resolvent_empiricalMeasure (α n) hw

/-- Each finite empirical transform is holomorphic on the exterior disk. -/
theorem differentiableOn_empiricalCauchyTransform
    (α : ∀ n, Fin (n + 1) → UnitDisk) (n : ℕ) :
    DifferentiableOn ℂ (empiricalCauchyTransform α n) exterior := by
  have hterm : ∀ j : Fin (n + 1),
      DifferentiableOn ℂ (fun w : ℂ ↦ (w - (α n j : ℂ))⁻¹) exterior := by
    intro j
    apply (differentiableOn_id.sub
      (differentiableOn_const (c := (α n j : ℂ)))).inv
    intro w hw hzero
    have heq : w = (α n j : ℂ) := sub_eq_zero.mp hzero
    have hz : ‖(α n j : ℂ)‖ ≤ 1 := by
      have hz' := (α n j).property
      change dist (α n j : ℂ) 0 ≤ 1 at hz'
      simpa [dist_zero_right] using hz'
    rw [heq] at hw
    exact (not_lt_of_ge hz) hw
  have hfinite : DifferentiableOn ℂ (finiteCauchyTransform α n) exterior := by
    unfold finiteCauchyTransform
    apply (differentiableOn_const (c := ((n + 1 : ℂ)⁻¹))).mul
    exact DifferentiableOn.fun_sum (u := Finset.univ) fun j _ ↦ hterm j
  exact hfinite.congr fun w hw ↦ empiricalCauchyTransform_eq_finite α n hw

/-- A common denominator lower bound gives a common Lipschitz estimate for
all probability Cauchy transforms. -/
theorem dist_cauchyTransform_le_of_norm_sub
    (ν : ProbabilityMeasure UnitDisk) {v w : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hv : 1 < ‖v‖) (hw : 1 < ‖w‖)
    (hvδ : ∀ z : UnitDisk, δ ≤ ‖v - (z : ℂ)‖)
    (hwδ : ∀ z : UnitDisk, δ ≤ ‖w - (z : ℂ)‖) :
    dist (cauchyTransform ν v) (cauchyTransform ν w) ≤
      δ⁻¹ ^ 2 * dist v w := by
  have hkernel : ∀ z : UnitDisk,
      dist ((v - (z : ℂ))⁻¹) ((w - (z : ℂ))⁻¹) ≤ δ⁻¹ ^ 2 * dist v w := by
    intro z
    have hv0 : v - (z : ℂ) ≠ 0 := by
      exact norm_pos_iff.mp (lt_of_lt_of_le hδ (hvδ z))
    have hw0 : w - (z : ℂ) ≠ 0 := by
      exact norm_pos_iff.mp (lt_of_lt_of_le hδ (hwδ z))
    rw [dist_inv_inv₀ hv0 hw0]
    have hprod : δ * δ ≤ ‖v - (z : ℂ)‖ * ‖w - (z : ℂ)‖ :=
      mul_le_mul (hvδ z) (hwδ z) hδ.le (norm_nonneg _)
    have hinv : (‖v - (z : ℂ)‖ * ‖w - (z : ℂ)‖)⁻¹ ≤ (δ * δ)⁻¹ :=
      inv_anti₀ (mul_pos hδ hδ) hprod
    have hdist : dist (v - (z : ℂ)) (w - (z : ℂ)) = dist v w := by
      simp [dist_eq_norm]
    rw [hdist, div_eq_mul_inv]
    calc
      dist v w * (‖v - (z : ℂ)‖ * ‖w - (z : ℂ)‖)⁻¹
          ≤ dist v w * (δ * δ)⁻¹ := mul_le_mul_of_nonneg_left hinv dist_nonneg
      _ = δ⁻¹ ^ 2 * dist v w := by
        field_simp
  have hiv : Integrable (fun z : UnitDisk ↦ (v - (z : ℂ))⁻¹)
      (ν : Measure UnitDisk) :=
    (boundedCauchyKernel v hv).integrable _
  have hiw : Integrable (fun z : UnitDisk ↦ (w - (z : ℂ))⁻¹)
      (ν : Measure UnitDisk) :=
    (boundedCauchyKernel w hw).integrable _
  rw [dist_eq_norm, cauchyTransform, cauchyTransform, ← integral_sub hiv hiw]
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := (ν : Measure UnitDisk))
      (ae_of_all _ (fun z ↦ by simpa only [dist_eq_norm] using hkernel z)))

/-- Restrict a probability Cauchy transform to the exterior subtype. -/
noncomputable def exteriorTransform
    (ν : ProbabilityMeasure UnitDisk) (w : exterior) : ℂ :=
  cauchyTransform ν w

/-- Probability Cauchy transforms form an equicontinuous family on the
exterior.  Locally, the distance to the unit disk gives a common resolvent
Lipschitz constant. -/
theorem equicontinuous_exteriorTransform :
    Equicontinuous (fun ν : ProbabilityMeasure UnitDisk ↦ exteriorTransform ν) := by
  intro w₀
  let δ : ℝ := (‖(w₀ : ℂ)‖ - 1) / 2
  have hδ : 0 < δ := by
    have hw₀ := w₀.property
    change 1 < ‖(w₀ : ℂ)‖ at hw₀
    dsimp [δ]
    linarith
  apply Metric.equicontinuousAt_of_continuity_modulus
      (fun w : exterior ↦ (δ ^ 2)⁻¹ * dist w w₀)
  · have hd : ContinuousAt (fun w : exterior ↦ dist w w₀) w₀ :=
      continuousAt_id.dist continuousAt_const
    have hd0 : Tendsto (fun w : exterior ↦ dist w w₀) (𝓝 w₀) (𝓝 0) := by
      change Tendsto (fun w : exterior ↦ dist w w₀) (𝓝 w₀) (𝓝 (dist w₀ w₀)) at hd
      simpa only [dist_self] using hd
    simpa only [mul_zero] using (tendsto_const_nhds (x := (δ ^ 2)⁻¹)).mul hd0
  · filter_upwards [Metric.ball_mem_nhds w₀ hδ] with w hw ν
    have hw_dist : dist (w : ℂ) (w₀ : ℂ) < δ := by
      simpa [Subtype.dist_eq] using hw
    have hw_norm : ‖(w₀ : ℂ)‖ - ‖(w : ℂ)‖ ≤ dist (w : ℂ) (w₀ : ℂ) := by
      simpa [dist_eq_norm, norm_sub_rev] using
        (norm_sub_norm_le (w₀ : ℂ) (w : ℂ))
    have hw_gap : 1 + δ ≤ ‖(w : ℂ)‖ := by
      dsimp [δ] at hw_dist ⊢
      linarith
    have hwδ : ∀ z : UnitDisk, δ ≤ ‖(w : ℂ) - (z : ℂ)‖ := by
      intro z
      have hz : ‖(z : ℂ)‖ ≤ 1 := by
        have hz' := z.property
        change dist (z : ℂ) 0 ≤ 1 at hz'
        simpa [dist_zero_right] using hz'
      have hrev := norm_sub_norm_le (w : ℂ) (z : ℂ)
      linarith
    have hw₀δ : ∀ z : UnitDisk, δ ≤ ‖(w₀ : ℂ) - (z : ℂ)‖ := by
      intro z
      have hz : ‖(z : ℂ)‖ ≤ 1 := by
        have hz' := z.property
        change dist (z : ℂ) 0 ≤ 1 at hz'
        simpa [dist_zero_right] using hz'
      have hrev := norm_sub_norm_le (w₀ : ℂ) (z : ℂ)
      dsimp [δ] at hδ ⊢
      linarith
    simpa [exteriorTransform, Subtype.dist_eq, dist_comm] using
      dist_cauchyTransform_le_of_norm_sub ν hδ w₀.property w.property hw₀δ hwδ

/-- Weak convergence of probability measures on the unit disk gives locally
uniform convergence of their Cauchy transforms throughout the exterior. -/
theorem cauchyTransform_tendstoLocallyUniformlyOn_of_weak
    {μ : ℕ → ProbabilityMeasure UnitDisk} {ν : ProbabilityMeasure UnitDisk}
    (hμ : Tendsto μ atTop (𝓝 ν)) :
    TendstoLocallyUniformlyOn (fun n ↦ cauchyTransform (μ n))
      (cauchyTransform ν) atTop exterior := by
  let _ : LocallyCompactSpace exterior := isOpen_exterior.locallyCompactSpace
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe,
    tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → exterior → ℂ := fun n ↦ exteriorTransform (μ n)
  let f : exterior → ℂ := exteriorTransform ν
  have hF : Equicontinuous F := by
    exact equicontinuous_exteriorTransform.comp μ
  have hFK : Equicontinuous (fun n ↦ fun x : K ↦ F n x) := by
    exact (equicontinuous_restrict_iff F).2 (hF.equicontinuousOn K)
  have hpoint : Tendsto (fun n ↦ fun x : K ↦ F n x) atTop
      (𝓝 (fun x : K ↦ f x)) := by
    rw [tendsto_pi_nhds]
    intro x
    exact cauchyTransform_tendsto_of_weak hμ x x.val.property
  have hu : Tendsto
      (UniformFun.ofFun ∘ fun n ↦ fun x : K ↦ F n x) atTop
      (𝓝 (UniformFun.ofFun (fun x : K ↦ f x))) :=
    (hFK.tendsto_uniformFun_iff_pi atTop (fun x : K ↦ f x)).2 hpoint
  have huniform : TendstoUniformly (fun n ↦ fun x : K ↦ F n x)
      (fun x : K ↦ f x) atTop := by
    exact UniformFun.tendsto_iff_tendstoUniformly.mp hu
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  change TendstoUniformly
    (fun n (x : K) ↦ cauchyTransform (μ n) ((x : exterior) : ℂ))
    (fun x : K ↦ cauchyTransform ν ((x : exterior) : ℂ)) atTop
  simpa [F, f, exteriorTransform] using huniform

/-- **Lemma 4.1, constant-limit conclusion.**  If the empirical Cauchy
transforms of an arbitrary triangular array in the closed unit disk converge
pointwise to a constant on a nonempty open subset of the exterior, then that
constant is zero. -/
theorem constant_limit_empiricalCauchyTransform_eq_zero
    (α : ∀ n, Fin (n + 1) → UnitDisk) (V : Set ℂ) (c : ℂ)
    (hVopen : IsOpen V) (hVne : V.Nonempty) (hVext : V ⊆ exterior)
    (hconv : ∀ w ∈ V,
      Tendsto (fun n ↦ empiricalCauchyTransform α n w) atTop (𝓝 c)) :
    c = 0 := by
  let μ : ℕ → ProbabilityMeasure UnitDisk := fun n ↦ empiricalMeasure (α n)
  obtain ⟨ν, φ, hφ, hweak, _⟩ := exists_cauchyTransform_tendsto_subseq μ
  have hlu : TendstoLocallyUniformlyOn
      (fun n ↦ cauchyTransform ((μ ∘ φ) n)) (cauchyTransform ν) atTop exterior :=
    cauchyTransform_tendstoLocallyUniformlyOn_of_weak hweak
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (cauchyTransform ((μ ∘ φ) n)) exterior := by
    filter_upwards with n
    change DifferentiableOn ℂ (empiricalCauchyTransform α (φ n)) exterior
    exact differentiableOn_empiricalCauchyTransform α (φ n)
  have hlimitDiff : DifferentiableOn ℂ (cauchyTransform ν) exterior :=
    hlu.differentiableOn hdiff isOpen_exterior
  have hlimitAnalytic : AnalyticOnNhd ℂ (cauchyTransform ν) exterior :=
    hlimitDiff.analyticOnNhd isOpen_exterior
  have hconstV : Set.EqOn (cauchyTransform ν) (fun _ ↦ c) V := by
    intro w hw
    have hlim := hlu.tendsto_at (hVext hw)
    have hcsub : Tendsto (fun n ↦ empiricalCauchyTransform α (φ n) w)
        atTop (𝓝 c) := (hconv w hw).comp hφ.tendsto_atTop
    have hlim' : Tendsto (fun n ↦ empiricalCauchyTransform α (φ n) w)
        atTop (𝓝 (cauchyTransform ν w)) := by
      simpa [μ, empiricalCauchyTransform, Function.comp_apply] using hlim
    exact tendsto_nhds_unique hlim' hcsub
  obtain ⟨w₀, hw₀⟩ := hVne
  have heventually : cauchyTransform ν =ᶠ[𝓝 w₀] fun _ ↦ c :=
    mem_of_superset (hVopen.mem_nhds hw₀) hconstV
  have hglobal : Set.EqOn (cauchyTransform ν) (fun _ ↦ c) exterior :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hlimitAnalytic analyticOnNhd_const isPreconnected_exterior
      (hVext hw₀) heventually
  exact constant_cauchyTransform_eq_zero ν c fun w hw ↦ hglobal hw

end Erdos973

#print axioms Erdos973.isPreconnected_exterior
#print axioms Erdos973.cauchyTransform_tendstoLocallyUniformlyOn_of_weak
#print axioms Erdos973.constant_limit_empiricalCauchyTransform_eq_zero
