import MerLeanExperiment.NetParameters

open MeasureTheory

namespace DiskDiscrepancy

/-- A proved per-disk tail estimate on the actual sample space yields one periodic set
controlling every disk up to the outer radius. The tail premise is discharged later. -/
theorem exists_periodic_grid_of_tail {L q K : ℕ} (hL : 0 < L) (hq : 0 < q)
    {R D : ℝ} (hR : 4 ≤ R) (hqR : R ≤ q) (hK : (q : ℝ) * (R + 1) ≤ K)
    (hcard : ((L * q : ℕ) : ℝ) ^ 2 * K ≤ 400 * R ^ 6)
    (μ : Measure ((Fin L × Fin L) → (Fin q × Fin q))) [IsProbabilityMeasure μ]
    (htail : ∀ x : Plane, ∀ r : ℝ, 0 < r → r ≤ R + 1 →
      μ.real {ω | D ≤ discrepancy (periodicGridSet L q hL hq ω) x r} ≤ 2 / R ^ 15) :
    ∃ ω : (Fin L × Fin L) → (Fin q × Fin q),
      ∀ x : Plane, ∀ r : ℝ, 0 < r → r ≤ R →
        discrepancy (periodicGridSet L q hL hq ω) x r ≤ D + 40 * Real.pi := by
  classical
  let E : ((Fin (L * q) × Fin (L * q)) × Fin K) →
      Set ((Fin L × Fin L) → (Fin q × Fin q)) := fun v ↦
    if 0 < (v.2.val : ℝ) / q ∧ (v.2.val : ℝ) / q ≤ R + 1 then
      {ω | D ≤ discrepancy (periodicGridSet L q hL hq ω)
        (centerGridPoint L q v.1) ((v.2.val : ℝ) / q)}
    else ∅
  have hR0 : 0 < R := by linarith
  have hE (v : (Fin (L * q) × Fin (L * q)) × Fin K) : μ.real (E v) ≤ 2 / R ^ 15 := by
    dsimp [E]
    split_ifs with h
    · exact htail _ _ h.1 h.2
    · simp only [measureReal_empty]
      positivity
  have hN : (Fintype.card ((Fin (L * q) × Fin (L * q)) × Fin K) : ℝ) ≤ 400 * R ^ 6 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using hcard
  obtain ⟨ω,hω⟩ := exists_avoiding_finite_events μ E hE
    (polynomial_net_probability_lt_one hR hN)
  refine ⟨ω, periodic_grid_bound_of_net hL hq ω hR hqR hK ?_⟩
  intro v j hj hjR
  have h := hω (v,j)
  simp only [E, hj, hjR, and_self, ite_true, Set.mem_ofPred_eq] at h
  exact (lt_of_not_ge h).le

end DiskDiscrepancy
