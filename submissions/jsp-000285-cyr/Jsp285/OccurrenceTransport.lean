import Jsp285.InfiniteSums

/-! Transport subset-sum witnesses through injective maps of occurrence indices. -/

namespace Jsp285

open scoped BigOperators Pointwise

/-- An injective map of occurrence indices transports every finite indexed
subset sum to the image support. -/
lemma indexedSubsetSums_comp_subset_image
    {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (v : κ → ℕ) (S : Set ι) :
    indexedSubsetSums (v ∘ f) S ⊆ indexedSubsetSums v (f '' S) := by
  classical
  rintro x ⟨I, hI, rfl⟩
  refine ⟨I.image f, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨i, hI hi, rfl⟩
  · rw [Finset.sum_image hf.injOn]
    rfl

/-- Sums of a shifted occurrence sequence use only indices in its tail. -/
lemma indexedSubsetSums_tail_subset (r : ℕ → ℕ) (s : ℕ) :
    indexedSubsetSums (fun i => r (s + i)) Set.univ ⊆
      indexedSubsetSums r (Set.Ici s) := by
  let f : ℕ → ℕ := fun i => s + i
  have hf : Function.Injective f := fun _ _ h => Nat.add_left_cancel h
  have htransport := indexedSubsetSums_comp_subset_image f hf r Set.univ
  apply htransport.trans
  apply indexedSubsetSums_mono r
  rintro _ ⟨i, -, rfl⟩
  exact Nat.le_add_right s i

/-- Finite prefix occurrence sums are finite indexed sums supported below the
prefix endpoint. -/
lemma occurrenceSums_range_subset_indexedSubsetSums_Iio
    (r : ℕ → ℕ) (s : ℕ) :
    (occurrenceSums r (Finset.range s) : Set ℕ) ⊆
      indexedSubsetSums r (Set.Iio s) := by
  rw [← indexedSubsetSums_finset]
  apply indexedSubsetSums_mono r
  intro i hi
  exact Finset.mem_range.mp hi

/-- Sums transported from two disjoint injective index streams combine into
an indexed subset sum of the original occurrence sequence. -/
lemma add_indexedSubsetSums_comp_subset
    (A : ℕ → ℕ) (β ρ : ℕ → ℕ)
    (hβ : Function.Injective β) (hρ : Function.Injective ρ)
    (hdisj : Disjoint (Set.range β) (Set.range ρ)) :
    indexedSubsetSums (A ∘ β) Set.univ +
        indexedSubsetSums (A ∘ ρ) Set.univ ⊆
      indexedSubsetSums A Set.univ := by
  rintro x ⟨b, hb, r, hr, rfl⟩
  have hb' : b ∈ indexedSubsetSums A (Set.range β) := by
    simpa only [Set.image_univ] using
      indexedSubsetSums_comp_subset_image β hβ A Set.univ hb
  have hr' : r ∈ indexedSubsetSums A (Set.range ρ) := by
    simpa only [Set.image_univ] using
      indexedSubsetSums_comp_subset_image ρ hρ A Set.univ hr
  exact indexedSubsetSums_mono A (Set.union_subset (Set.subset_univ _)
    (Set.subset_univ _)) (add_mem_indexedSubsetSums A hdisj hb' hr')

end Jsp285
