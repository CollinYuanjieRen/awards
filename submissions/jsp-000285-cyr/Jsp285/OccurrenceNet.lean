import Jsp285.InfiniteSums
import ErdosProblems.Erdos344

/-! Graham's additive-net construction for arbitrary occurrence sequences. -/

namespace Jsp285

open scoped BigOperators

/-- Sum of the occurrences strictly before index `n`. -/
def occurrencePrefixSum (y : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, y i

/-- The occurrence-indexed form of the prefix approximation lemma used in
Graham's additive-net construction in `Erdos344`. -/
private lemma exists_prefix_occurrenceSum_near (y : ℕ → ℕ) (m₀ : ℕ)
    (hgrowth : ∀ m, m₀ ≤ m → y m ≤ occurrencePrefixSum y m) :
    ∀ n, m₀ ≤ n → ∀ x ≤ occurrencePrefixSum y n,
      ∃ F : Finset ℕ, F ⊆ Finset.range n ∧
        (∑ i ∈ F, y i) ≤ x ∧
          x ≤ (∑ i ∈ F, y i) + occurrencePrefixSum y m₀ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro x hx
      exact ⟨∅, by simp, by simp, by simpa using hx⟩
  | succ n hn ih =>
      intro x hx
      by_cases hsmall : x ≤ occurrencePrefixSum y n
      · obtain ⟨F, hF, hFlo, hFhi⟩ := ih x hsmall
        exact ⟨F, hF.trans (by simp), hFlo, hFhi⟩
      · have hyn : y n ≤ occurrencePrefixSum y n := hgrowth n hn
        have hyx : y n ≤ x := hyn.trans (Nat.le_of_lt (Nat.lt_of_not_ge hsmall))
        have hsub : x - y n ≤ occurrencePrefixSum y n := by
          rw [occurrencePrefixSum, Finset.sum_range_succ,
            ← occurrencePrefixSum] at hx
          omega
        obtain ⟨F, hF, hFlo, hFhi⟩ := ih (x - y n) hsub
        have hnF : n ∉ F := fun h => by
          have := hF h
          simp at this
        refine ⟨insert n F, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · exact Finset.mem_range.mpr
              ((Finset.mem_range.mp (hF hi)).trans (Nat.lt_succ_self n))
        · rw [Finset.sum_insert hnF]
          omega
        · rw [Finset.sum_insert hnF]
          omega

/-- A positive occurrence sequence in one residue subgroup, satisfying
Graham's eventual prefix-growth condition, has an additive net of indexed
subset sums.  Repeated values remain distinct occurrences. -/
theorem exists_addNet_indexedSubsetSums {q : ℕ} (hq : 0 < q)
    (y : ℕ → ℕ) (hypos : ∀ i, 0 < y i) (hyq : ∀ i, q ∣ y i)
    (hgrowth : ∃ m₀, ∀ m, m₀ ≤ m → y m ≤ occurrencePrefixSum y m) :
    ∃ K, Erdos344.IsAddNet q K (indexedSubsetSums y Set.univ) := by
  obtain ⟨m₀, hgrowth⟩ := hgrowth
  let K := occurrencePrefixSum y m₀
  refine ⟨K, hq, ?_⟩
  intro n
  let x := (n + K) * q
  let N := max m₀ x
  have hmN : m₀ ≤ N := le_max_left _ _
  have hxN : x ≤ N := le_max_right _ _
  have hid : N ≤ occurrencePrefixSum y N := by
    calc
      N = ∑ _i ∈ Finset.range N, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range N, y i := by
        exact Finset.sum_le_sum fun i _ => hypos i
      _ = occurrencePrefixSum y N := rfl
  have hxsum : x ≤ occurrencePrefixSum y N := hxN.trans hid
  obtain ⟨F, hFN, hFlo, hFhi⟩ :=
    exists_prefix_occurrenceSum_near y m₀ hgrowth N hmN x hxsum
  let s := ∑ i ∈ F, y i
  have hmem : s ∈ indexedSubsetSums y Set.univ := by
    exact ⟨F, Set.subset_univ _, rfl⟩
  have hdiv : q ∣ s := by
    exact Finset.dvd_sum fun i _ => hyq i
  have hKq : K ≤ K * q := by
    have : 1 ≤ q := hq
    nlinarith
  refine ⟨s, hmem, hdiv, ?_, ?_⟩
  · have hFhi' : x ≤ s + K * q := by
      exact hFhi.trans (Nat.add_le_add_left (by simpa [K] using hKq) _)
    dsimp [x] at hFhi'
    rw [Nat.add_mul] at hFhi'
    exact Nat.le_of_add_le_add_right hFhi'
  · exact hFlo

end Jsp285
