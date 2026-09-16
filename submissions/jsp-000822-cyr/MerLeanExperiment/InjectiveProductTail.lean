import MerLeanExperiment.FiniteProductTail

open MeasureTheory

namespace DiskDiscrepancy

noncomputable section

variable {I J V : Type*} [Fintype I] [Fintype V] [Nonempty V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Functions of distinct selected coordinates are independent under the
actual finite uniform product measure. -/
theorem iIndepFun_uniformProduct_comp_injective (g : J → I) (hg : Function.Injective g)
    (X : J → V → ℝ) :
    ProbabilityTheory.iIndepFun (fun j (ω : I → V) ↦ X j (ω (g j)))
      (Measure.pi (fun _ : I ↦ (PMF.uniformOfFintype V).toMeasure)) := by
  have hall : ProbabilityTheory.iIndepFun (fun i (ω : I → V) ↦ ω i)
      (Measure.pi (fun _ : I ↦ (PMF.uniformOfFintype V).toMeasure)) := by
    exact ProbabilityTheory.iIndepFun_pi fun _ ↦ measurable_id.aemeasurable
  have hselected := hall.precomp hg
  exact hselected.comp X (fun j ↦ (measurable_of_finite (X j)))

theorem uniformProduct_injective_centered_sum_tail [Fintype J]
    (g : J → I) (hg : Function.Injective g) (X : J → V → ℝ)
    (hX0 : ∀ j v, 0 ≤ X j v) (hX1 : ∀ j v, X j v ≤ 1)
    (B : Finset J) (hB : B.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    let μ : Measure (I → V) :=
      Measure.pi (fun _ : I ↦ (PMF.uniformOfFintype V).toMeasure)
    let Z : (I → V) → ℝ := fun ω ↦
      ∑ j ∈ B, (X j (ω (g j)) - ∫ ω' : I → V, X j (ω' (g j)) ∂μ)
    μ.real {ω | t ≤ |Z ω|} ≤ 2 * Real.exp (-2 * t ^ 2 / B.card) := by
  dsimp
  let μ : Measure (I → V) :=
    Measure.pi (fun _ : I ↦ (PMF.uniformOfFintype V).toMeasure)
  let Y : J → (I → V) → ℝ := fun j ω ↦
    X j (ω (g j)) - ∫ ω' : I → V, X j (ω' (g j)) ∂μ
  change μ.real {ω | t ≤ |∑ j ∈ B, Y j ω|} ≤ 2 * Real.exp (-2 * t ^ 2 / B.card)
  have hindep := iIndepFun_uniformProduct_comp_injective g hg X
  have hsub (j : J) : ProbabilityTheory.HasSubgaussianMGF (Y j) (1 / 4) μ := by
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (a := 0) (b := 1) (μ := μ)
      ((measurable_of_finite (fun ω : I → V ↦ X j (ω (g j)))).aemeasurable)
      (Filter.Eventually.of_forall fun ω ↦ ⟨hX0 j (ω (g j)), hX1 j (ω (g j))⟩)
    convert h using 1
    norm_num
  have hindepY : ProbabilityTheory.iIndepFun Y μ := by
    have hc := hindep.comp
      (fun j x ↦ x - ∫ ω' : I → V, X j (ω' (g j)) ∂μ)
      (fun _ ↦ measurable_id.sub measurable_const)
    simpa [Y, μ, Function.comp_def] using hc
  have hpos := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hindepY (s := B) (c := fun _ ↦ 1 / 4) (fun j _ ↦ hsub j) ht
  have hindepNeg : ProbabilityTheory.iIndepFun (fun j ω ↦ -(Y j ω)) μ :=
    hindepY.comp (fun _ x ↦ -x) (fun _ ↦ measurable_neg)
  have hneg := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hindepNeg (s := B) (c := fun _ ↦ 1 / 4) (fun j _ ↦ (hsub j).neg) ht
  have hparam : (2 : ℝ) * (↑(∑ _j ∈ B, (1 / 4 : NNReal))) = B.card / 2 := by
    simp
    field_simp
    norm_num
  rw [hparam] at hpos hneg
  have hexp : Real.exp (-t ^ 2 / (B.card / 2)) = Real.exp (-2 * t ^ 2 / B.card) := by
    have hcard : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    congr 1
    field_simp
  rw [hexp] at hpos hneg
  have hu := measureReal_union_le (μ := μ)
    {ω | t ≤ ∑ j ∈ B, Y j ω} {ω | t ≤ ∑ j ∈ B, -(Y j ω)}
  have he : {ω | t ≤ |∑ j ∈ B, Y j ω|} =
      {ω | t ≤ ∑ j ∈ B, Y j ω} ∪ {ω | t ≤ ∑ j ∈ B, -(Y j ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib]
    rw [le_abs]
  rw [he]
  linarith

end

end DiskDiscrepancy
