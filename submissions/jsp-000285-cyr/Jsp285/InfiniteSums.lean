import Jsp285.OccurrenceSums

/-! Finite occurrence subset sums drawn from a possibly infinite index set. -/

namespace Jsp285

/-- A finite selection of occurrence indices from `S`, with their actual weights. -/
def indexedSubsetSums {ι : Type*} (v : ι → ℕ) (S : Set ι) : Set ℕ :=
  {x | ∃ I : Finset ι, (↑I : Set ι) ⊆ S ∧ x = ∑ i ∈ I, v i}

/-- The finite and infinite representations agree on finite index sets. -/
lemma indexedSubsetSums_finset {ι : Type*} (v : ι → ℕ) (I : Finset ι) :
    indexedSubsetSums v (↑I : Set ι) = (occurrenceSums v I : Set ℕ) := by
  ext x
  simp only [indexedSubsetSums, Set.mem_ofPred_eq, Finset.coe_subset,
    Finset.mem_coe, mem_occurrenceSums]
  exact exists_congr fun J ↦ and_congr_right fun _ ↦ eq_comm

/-- Enlarging the allowed index set preserves each witnessed sum. -/
lemma indexedSubsetSums_mono {ι : Type*} (v : ι → ℕ) {S T : Set ι}
    (hST : S ⊆ T) : indexedSubsetSums v S ⊆ indexedSubsetSums v T := by
  rintro x ⟨I, hI, rfl⟩
  exact ⟨I, hI.trans hST, rfl⟩

/-- Disjoint occurrence supports permit adding their finite sums. -/
lemma add_mem_indexedSubsetSums {ι : Type*} (v : ι → ℕ) {S T : Set ι}
    (hST : Disjoint S T) {x y : ℕ}
    (hx : x ∈ indexedSubsetSums v S) (hy : y ∈ indexedSubsetSums v T) :
    x + y ∈ indexedSubsetSums v (S ∪ T) := by
  classical
  obtain ⟨I, hI, rfl⟩ := hx
  obtain ⟨J, hJ, rfl⟩ := hy
  have hIJ : Disjoint I J := Finset.disjoint_left.mpr fun i hi hj ↦
    Set.disjoint_left.mp hST (hI hi) (hJ hj)
  refine ⟨I ∪ J, ?_, (Finset.sum_union hIJ).symm⟩
  intro i hi
  exact (Finset.mem_union.mp hi).elim (fun h ↦ Or.inl (hI h))
    (fun h ↦ Or.inr (hJ h))

end Jsp285
