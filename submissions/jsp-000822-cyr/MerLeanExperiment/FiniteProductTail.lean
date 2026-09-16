import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DiskDiscrepancy

noncomputable section

variable {V ι : Type*} [Fintype V] [Nonempty V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Fintype ι]

/-- A coordinate expectation under the finite uniform product measure is the
literal uniform finite average. -/
theorem uniformProduct_coordinate_expectation (i : ι) (X : V → ℝ) :
    (∫ ω : ι → V, X (ω i) ∂Measure.pi
      (fun _ : ι ↦ (PMF.uniformOfFintype V).toMeasure)) =
      ∑ v : V, ((Fintype.card V : ℝ)⁻¹ * X v) := by
  let ν : Measure V := (PMF.uniformOfFintype V).toMeasure
  have hp := measurePreserving_eval (fun _ : ι ↦ ν) i
  have hmap : (∫ ω : ι → V, X (ω i) ∂Measure.pi (fun _ : ι ↦ ν)) = ∫ v, X v ∂ν := by
    calc
      (∫ ω : ι → V, X (ω i) ∂Measure.pi (fun _ : ι ↦ ν)) =
          ∫ v, X v ∂Measure.map (fun ω : ι → V ↦ ω i) (Measure.pi (fun _ : ι ↦ ν)) :=
        (integral_map_of_stronglyMeasurable
          (φ := fun ω : ι → V ↦ ω i) (f := X) (measurable_pi_apply i)
          (measurable_of_finite X).stronglyMeasurable).symm
      _ = ∫ v, X v ∂ν := by rw [hp.map_eq]
  rw [hmap]
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, smul_eq_mul]

/-- Two-sided Hoeffding bound for bounded coordinate functions on the actual
finite uniform product probability space. Independence is derived from the
product measure rather than assumed. -/
theorem uniformProduct_centered_sum_tail (X : ι → V → ℝ)
    (hX0 : ∀ i v, 0 ≤ X i v) (hX1 : ∀ i v, X i v ≤ 1)
    (B : Finset ι) (hB : B.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    let ν : Measure V := (PMF.uniformOfFintype V).toMeasure
    let μ : Measure (ι → V) := Measure.pi (fun _ : ι ↦ ν)
    let Z : (ι → V) → ℝ := fun ω ↦
      ∑ i ∈ B, (X i (ω i) - ∫ ω' : ι → V, X i (ω' i) ∂μ)
    μ.real {ω | t ≤ |Z ω|} ≤ 2 * Real.exp (-2 * t ^ 2 / B.card) := by
  dsimp
  let ν : Measure V := (PMF.uniformOfFintype V).toMeasure
  let μ : Measure (ι → V) := Measure.pi (fun _ : ι ↦ ν)
  let Y : ι → (ι → V) → ℝ := fun i ω ↦
    X i (ω i) - ∫ ω' : ι → V, X i (ω' i) ∂μ
  change μ.real {ω | t ≤ |∑ i ∈ B, Y i ω|} ≤
    2 * Real.exp (-2 * t ^ 2 / B.card)
  have hmeas (i : ι) : AEMeasurable (fun ω : ι → V ↦ X i (ω i)) μ := by
    exact (measurable_of_finite _).aemeasurable
  have hindep : ProbabilityTheory.iIndepFun
      (fun (i : ι) (ω : ι → V) ↦ X i (ω i)) μ := by
    exact ProbabilityTheory.iIndepFun_pi fun i ↦
      (measurable_of_finite (X i)).aemeasurable
  have hsub (i : ι) : ProbabilityTheory.HasSubgaussianMGF (Y i) (1 / 4) μ := by
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (hmeas i)
      (Filter.Eventually.of_forall fun ω ↦ ⟨hX0 i (ω i), hX1 i (ω i)⟩)
    convert h using 1
    norm_num
  have hindepY : ProbabilityTheory.iIndepFun Y μ := by
    have hc := hindep.comp
      (fun i x ↦ x - ∫ ω' : ι → V, X i (ω' i) ∂μ)
      (fun _ ↦ measurable_id.sub measurable_const)
    simpa [Y, Function.comp_def] using hc
  have hpos := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hindepY (s := B) (c := fun _ ↦ 1 / 4) (fun (i : ι) _ ↦ hsub i) ht
  have hindep_neg : ProbabilityTheory.iIndepFun (fun (i : ι) ω ↦ -(Y i ω)) μ := by
    exact hindepY.comp (fun _ x ↦ -x) (fun _ ↦ measurable_neg)
  have hneg := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hindep_neg (s := B) (c := fun _ ↦ 1 / 4) (fun (i : ι) _ ↦ (hsub i).neg) ht
  have hcardpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hparam : (2 : ℝ) * (↑(∑ _i ∈ B, (1 / 4 : NNReal))) = B.card / 2 := by
    simp
    field_simp
    norm_num
  rw [hparam] at hpos hneg
  have hexp : Real.exp (-t ^ 2 / (B.card / 2)) =
      Real.exp (-2 * t ^ 2 / B.card) := by
    congr 1
    field_simp
  rw [hexp] at hpos hneg
  have hunion := measureReal_union_le
    (μ := μ) {ω | t ≤ ∑ i ∈ B, Y i ω} {ω | t ≤ ∑ i ∈ B, -(Y i ω)}
  have hevent : {ω | t ≤ |∑ i ∈ B, Y i ω|} =
      {ω | t ≤ ∑ i ∈ B, Y i ω} ∪ {ω | t ≤ ∑ i ∈ B, -(Y i ω)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Finset.sum_neg_distrib]
    rw [le_abs]
  rw [hevent]
  calc
    μ.real ({ω | t ≤ ∑ i ∈ B, Y i ω} ∪ {ω | t ≤ ∑ i ∈ B, -(Y i ω)}) ≤
        μ.real {ω | t ≤ ∑ i ∈ B, Y i ω} +
          μ.real {ω | t ≤ ∑ i ∈ B, -(Y i ω)} := hunion
    _ ≤ 2 * Real.exp (-2 * t ^ 2 / B.card) := by linarith

end

end DiskDiscrepancy
