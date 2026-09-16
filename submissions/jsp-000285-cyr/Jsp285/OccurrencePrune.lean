import Jsp285.OccurrenceDyadic

/-! Removing small dyadic classes of occurrence weights. -/

namespace Jsp285

/-- Remove every occurrence whose entire dyadic weight class has size below `Q`. -/
def dyadicPrune {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (Q : ℕ) : Finset ι :=
  Y.filter fun i ↦ Q ≤ (dyadicBin v Y (Nat.log 2 (v i))).card

/-- Dyadic pruning only removes occurrence indices. -/
lemma dyadicPrune_subset {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (Q : ℕ) :
    dyadicPrune v Y Q ⊆ Y :=
  Finset.filter_subset _ _

/-- Pruning either keeps an original dyadic bin whole or deletes it whole. -/
lemma dyadicBin_dyadicPrune {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (Q j : ℕ) :
    dyadicBin v (dyadicPrune v Y Q) j =
      if Q ≤ (dyadicBin v Y j).card then dyadicBin v Y j else ∅ := by
  ext i
  by_cases hlarge : Q ≤ (dyadicBin v Y j).card
  · rw [if_pos hlarge]
    constructor
    · intro hi
      have hiBin := Finset.mem_filter.mp hi
      have hiPrune := Finset.mem_filter.mp hiBin.1
      exact Finset.mem_filter.mpr ⟨hiPrune.1, hiBin.2⟩
    · intro hi
      have hiBin := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hiBin.1, ?_⟩, hiBin.2⟩
      simpa only [hiBin.2] using hlarge
  · rw [if_neg hlarge]
    constructor
    · intro hi
      have hiBin := Finset.mem_filter.mp hi
      have hiPrune := Finset.mem_filter.mp hiBin.1
      exact (hlarge <| by simpa only [hiBin.2] using hiPrune.2).elim
    · intro hi
      simp at hi

/-- Every dyadic bin left after pruning is empty or has at least `Q` occurrences. -/
lemma dyadicBin_dyadicPrune_large_or_empty {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (Q j : ℕ) :
    dyadicBin v (dyadicPrune v Y Q) j = ∅ ∨
      Q ≤ (dyadicBin v (dyadicPrune v Y Q) j).card := by
  rw [dyadicBin_dyadicPrune]
  by_cases hlarge : Q ≤ (dyadicBin v Y j).card
  · simp [hlarge]
  · simp [hlarge]

/-- Pruning small dyadic classes loses at most `Q` occurrences for each
possible logarithm of a positive weight bounded by `N`. -/
theorem card_sub_dyadicPrune_le {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (Y : Finset ι) (N Q : ℕ)
    (hY : ∀ i ∈ Y, 0 < v i ∧ v i ≤ N) :
    Y.card - (dyadicPrune v Y Q).card ≤ (Nat.log 2 N + 1) * Q := by
  rw [← Finset.card_sdiff_of_subset (dyadicPrune_subset v Y Q)]
  let Jsmall := (Finset.range (Nat.log 2 N + 1)).filter fun j ↦
    (dyadicBin v Y j).card < Q
  let U := Jsmall.biUnion fun j ↦ dyadicBin v Y j
  have hlost : Y \ dyadicPrune v Y Q ⊆ U := by
    intro i hi
    have hiY := (Finset.mem_sdiff.mp hi).1
    have hinot := (Finset.mem_sdiff.mp hi).2
    have hilog : Nat.log 2 (v i) < Nat.log 2 N + 1 :=
      Nat.lt_succ_of_le <| Nat.log_mono_right (hY i hiY).2
    have hismall : (dyadicBin v Y (Nat.log 2 (v i))).card < Q := by
      simpa only [dyadicPrune, Finset.mem_filter, hiY, true_and, not_le] using hinot
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 (v i), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hilog, hismall⟩
    · exact Finset.mem_filter.mpr ⟨hiY, rfl⟩
  have hUcard : U.card ≤ ∑ j ∈ Jsmall, (dyadicBin v Y j).card :=
    Finset.card_biUnion_le
  have hsum : (∑ j ∈ Jsmall, (dyadicBin v Y j).card) ≤ Jsmall.card * Q := by
    calc
      (∑ j ∈ Jsmall, (dyadicBin v Y j).card) ≤ ∑ _j ∈ Jsmall, Q := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.mem_filter.mp hj).2.le
      _ = Jsmall.card * Q := by simp
  have hJcard : Jsmall.card ≤ Nat.log 2 N + 1 := by
    calc
      Jsmall.card ≤ (Finset.range (Nat.log 2 N + 1)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.log 2 N + 1 := by simp
  calc
    (Y \ dyadicPrune v Y Q).card ≤ U.card := Finset.card_le_card hlost
    _ ≤ ∑ j ∈ Jsmall, (dyadicBin v Y j).card := hUcard
    _ ≤ Jsmall.card * Q := hsum
    _ ≤ (Nat.log 2 N + 1) * Q := Nat.mul_le_mul_right Q hJcard

end Jsp285
