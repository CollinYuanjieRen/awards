import Mathlib

/-!
Finite subset sums indexed by occurrences. Equal weights retain separate indices.
-/

namespace Jsp285

open scoped BigOperators Pointwise

variable {ι M : Type*} [AddCommMonoid M] [DecidableEq M]

/-- Sums of all subsets of a finite occurrence set. -/
def occurrenceSums (v : ι → M) (I : Finset ι) : Finset M :=
  I.powerset.image fun J ↦ ∑ i ∈ J, v i

/-- Membership exhibits the actual occurrences used, without identifying equal weights. -/
lemma mem_occurrenceSums {v : ι → M} {I : Finset ι} {x : M} :
    x ∈ occurrenceSums v I ↔ ∃ J ⊆ I, (∑ i ∈ J, v i) = x := by
  simp [occurrenceSums]

/-- The empty subset gives zero. -/
lemma zero_mem_occurrenceSums (v : ι → M) (I : Finset ι) :
    0 ∈ occurrenceSums v I := by
  exact mem_occurrenceSums.mpr ⟨∅, Finset.empty_subset _, by simp⟩

/-- Increasing the available occurrence set preserves every subset sum. -/
lemma occurrenceSums_mono (v : ι → M) {I J : Finset ι} (h : I ⊆ J) :
    occurrenceSums v I ⊆ occurrenceSums v J := by
  rintro x hx
  obtain ⟨K, hK, rfl⟩ := mem_occurrenceSums.mp hx
  exact mem_occurrenceSums.mpr ⟨K, hK.trans h, rfl⟩

/-- Sums supported on disjoint occurrence sets can be added without reuse. -/
lemma add_mem_occurrenceSums [DecidableEq ι] {v : ι → M} {I J : Finset ι}
    (hdisj : Disjoint I J) {x y : M}
    (hx : x ∈ occurrenceSums v I) (hy : y ∈ occurrenceSums v J) :
    x + y ∈ occurrenceSums v (I ∪ J) := by
  obtain ⟨K, hK, rfl⟩ := mem_occurrenceSums.mp hx
  obtain ⟨L, hL, rfl⟩ := mem_occurrenceSums.mp hy
  refine mem_occurrenceSums.mpr ⟨K ∪ L, Finset.union_subset_union hK hL, ?_⟩
  exact Finset.sum_union (hdisj.mono hK hL)

/-- With natural weights, every subset sum is bounded by the total mass. -/
lemma occurrenceSum_le_mass {v : ι → ℕ} {I : Finset ι} {x : ℕ}
    (hx : x ∈ occurrenceSums v I) : x ≤ ∑ i ∈ I, v i := by
  obtain ⟨J, hJ, rfl⟩ := mem_occurrenceSums.mp hx
  exact Finset.sum_le_sum_of_subset hJ

/-- Scaling each selected weight scales each subset sum. -/
lemma scale_mem_occurrenceSums {v w : ι → ℕ} {I J : Finset ι} {d x : ℕ}
    (hJI : J ⊆ I) (hscale : ∀ i ∈ J, d * w i = v i)
    (hx : x ∈ occurrenceSums w J) : d * x ∈ occurrenceSums v I := by
  obtain ⟨K, hK, rfl⟩ := mem_occurrenceSums.mp hx
  refine mem_occurrenceSums.mpr ⟨K, hK.trans hJI, ?_⟩
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi ↦ (hscale i (hK hi)).symm

end Jsp285
