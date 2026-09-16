import Jsp285.FixedStepFromBlocks
import Jsp285.OccurrenceBlocks

namespace Jsp285

/-- A positive occurrence sequence with an eventual linear bound has
arbitrarily long subset-sum progressions with one fixed positive step. -/
theorem fixedStep_of_linear_bound
    (b : ℕ → ℕ) (hpos : ∀ i : ℕ, 0 < b i)
    (hbound : ∃ I₀ : ℕ, ∀ i : ℕ, I₀ ≤ i → b i ≤ i / infiniteScale) :
    Erdos344.HasFixedStepProgressions (indexedSubsetSums b Set.univ) := by
  obtain ⟨I₀, hbound⟩ := hbound
  let L := max 2 I₀
  let B : ℕ → Finset ℕ := fun i ↦
    Finset.Ico (finiteCoefficient * blockLength L i)
      (2 * finiteCoefficient * blockLength L i)
  have hL : 2 ≤ L := Nat.le_max_left _ _
  have hI₀L : I₀ ≤ L := Nat.le_max_right _ _
  have hlengthMono : ∀ {i j : ℕ}, i ≤ j →
      blockLength L i ≤ blockLength L j := by
    intro i j hij
    exact Nat.mul_le_mul_right L (Nat.pow_le_pow_right (by omega) hij)
  have hnext (i : ℕ) : blockLength L (i + 1) = 2 * blockLength L i := by
    simp [blockLength, pow_succ]
    ring
  have hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hxi' := Finset.mem_Ico.mp hxi
    have hxj' := Finset.mem_Ico.mp hxj
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hsep : 2 * finiteCoefficient * blockLength L i ≤
          finiteCoefficient * blockLength L j := by
        calc
          2 * finiteCoefficient * blockLength L i =
              finiteCoefficient * blockLength L (i + 1) := by rw [hnext]; ring
          _ ≤ finiteCoefficient * blockLength L j :=
            Nat.mul_le_mul_left finiteCoefficient (hlengthMono (by omega))
      omega
    · have hsep : 2 * finiteCoefficient * blockLength L j ≤
          finiteCoefficient * blockLength L i := by
        calc
          2 * finiteCoefficient * blockLength L j =
              finiteCoefficient * blockLength L (j + 1) := by rw [hnext]; ring
          _ ≤ finiteCoefficient * blockLength L i :=
            Nat.mul_le_mul_left finiteCoefficient (hlengthMono (by omega))
      omega
  have hAP : ∀ i, ∃ a d : ℕ, 0 < d ∧
      16 * d ≤ blockLength L i ∧
      ∀ j < blockLength L i, a + j * d ∈ occurrenceSums b (B i) := by
    intro i
    have hLLi : L ≤ blockLength L i := by
      simpa [blockLength] using hlengthMono (i := 0) (j := i) (Nat.zero_le i)
    have hstart : I₀ ≤ finiteCoefficient * blockLength L i := by
      apply hI₀L.trans <| hLLi.trans ?_
      exact Nat.le_mul_of_pos_left _ finiteCoefficient_pos
    simpa only [B] using exists_small_step_block_AP b hpos I₀
      (blockLength L i) (hL.trans hLLi) hstart hbound
  obtain ⟨D, hD, hmerged⟩ :=
    exists_merged_occurrence_blocks b B L hL hdisj hAP
  exact fixedStep_of_merged_occurrence_blocks b B L D hL hD hmerged

end Jsp285
