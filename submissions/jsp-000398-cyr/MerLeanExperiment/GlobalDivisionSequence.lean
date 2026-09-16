import MerLeanExperiment.BlockConstruction
import MerLeanExperiment.SubdivisionEnumeration

open Filter Set
open scoped Topology

namespace Erdos492Real

noncomputable section

/-- Enumerating the actual glued endpoint set realizes all geometric conditions
in Schmidt's original real-subdivision question. -/
theorem exists_global_division_sequence (P : ℕ → FiniteDivision)
    (hFine : ∀ k, (P k).Fine (blockEpsilon k)) :
    ∃ a : ℕ → ℝ, a 0 = 0 ∧ StrictMono a ∧ Tendsto a atTop atTop ∧
      Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) ∧
      range a = globalEndpoints P ∧
      ∀ lam : ℝ, sequenceRegion a lam = lowerRegion (globalEndpoints P) lam := by
  obtain ⟨a, ha0, hmono, hrange, hatop⟩ := exists_endpoint_enumeration
    (globalEndpoints P) (zero_mem_globalEndpoints P) (globalEndpoints_nonneg P)
    (globalEndpoints_finite_Iic P) (globalEndpoints_unbounded P)
  refine ⟨a, ha0, hmono, hatop, ?_, hrange, ?_⟩
  · apply tendsto_ratio_of_bounded_gaps ha0 hmono hatop
    intro n
    exact global_consecutive_gap_le_one P hFine
      (endpoint_enumeration_consecutive hrange hmono n)
  · intro lam
    exact (lowerRegion_eq_sequenceRegion hrange hmono lam).symm

end

end Erdos492Real
