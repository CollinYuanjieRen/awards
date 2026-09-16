import Jsp285.Definitions
import Jsp285.DensitySelection
import Jsp285.LinearFixedStep
import Jsp285.OccurrenceEndgame

/-! The full eventual-density theorem for arbitrary occurrence-indexed multisets. -/

namespace Jsp285

/-- The auxiliary indexed-sum model is exactly the literal frozen object on all indices. -/
lemma indexedSubsetSums_univ_eq (A : ℕ → ℕ) :
    indexedSubsetSums A Set.univ = Erdos343.SubsetSums A := by
  ext x
  simp [indexedSubsetSums, Erdos343.SubsetSums]

/-- The proved finite theorem closes every input needed by the infinite extension. -/
theorem subcomplete_of_eventual_count (A : ℕ → ℕ) (hpos : ∀ i, 0 < A i)
    (hcount : Erdos343.HasEventualLinearCountingLowerBound infiniteCoefficient A) :
    Erdos343.IsSubcomplete A := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hcount
  let N₁ := max N₀ 1
  have hcount' : ∀ N, N₁ ≤ N → ∃ s : Finset ℕ,
      8 * infiniteScale * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N := by
    intro N hN
    exact hN₀ N ((le_max_left _ _).trans hN)
  obtain ⟨β, ρ, hβ, hρ, hdisj, I₀, hbound⟩ :=
    exists_two_linear_selections A infiniteScale N₁ infiniteScale_pos
      (le_max_right _ _) hcount'
  have hfixed := fixedStep_of_linear_bound (A ∘ β) (fun i ↦ hpos (β i))
    ⟨I₀, fun i hi ↦ (hbound i hi).1⟩
  have hAP := fixedStep_and_occurrence_residue_part (A ∘ β) (A ∘ ρ)
    (fun i ↦ hpos (ρ i)) infiniteScale two_le_infiniteScale
    ⟨I₀, fun i hi ↦ (hbound i hi).2⟩ hfixed
  have hfull := Erdos344.containsInfiniteAP_mono
    (add_indexedSubsetSums_comp_subset A β ρ hβ hρ hdisj) hAP
  rw [indexedSubsetSums_univ_eq] at hfull
  exact hfull

end Jsp285
