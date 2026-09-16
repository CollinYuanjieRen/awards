import Jsp285.MergedBlocks

namespace Jsp285

/-- If every merged occurrence block contains a long progression whose
positive step divides one fixed integer, one step occurs on infinitely many
blocks and gives arbitrarily long progressions in all indexed subset sums. -/
theorem fixedStep_of_merged_occurrence_blocks
    (v : ℕ → ℕ) (B : ℕ → Finset ℕ) (L D : ℕ)
    (hL : 2 ≤ L) (hD : 0 < D)
    (hmerged : ∀ i, ∃ a d : ℕ, 0 < d ∧ d ∣ D ∧
      ∀ j < blockLength L i / 2,
        a + j * d ∈ occurrenceSums v (usedBlocks B i)) :
    Erdos344.HasFixedStepProgressions (indexedSubsetSums v Set.univ) := by
  let aa : ℕ → ℕ := fun i => (hmerged i).choose
  let dd : ℕ → ℕ := fun i => (hmerged i).choose_spec.choose
  have hspec (i : ℕ) : 0 < dd i ∧ dd i ∣ D ∧
      ∀ j < blockLength L i / 2,
        aa i + j * dd i ∈ occurrenceSums v (usedBlocks B i) :=
    (hmerged i).choose_spec.choose_spec
  have hddle (i : ℕ) : dd i ≤ D :=
    Nat.le_of_dvd hD (hspec i).2.1
  let f : ℕ → Fin (D + 1) := fun i =>
    ⟨dd i, Nat.lt_succ_of_le (hddle i)⟩
  obtain ⟨w, hw⟩ := Finite.exists_infinite_fiber f
  have hwset : (f ⁻¹' {w}).Infinite := Set.infinite_coe_iff.mp hw
  have hwpos : 0 < w.val := by
    obtain ⟨i, hi, -⟩ := hwset.exists_gt 0
    have hfi : f i = w := by simpa using hi
    have hval := congrArg (fun x : Fin (D + 1) => x.val) hfi
    change dd i = w.val at hval
    simpa [← hval] using (hspec i).1
  refine ⟨w.val, hwpos, ?_⟩
  intro k
  obtain ⟨i, hiFiber, hki⟩ := hwset.exists_gt k
  have hfi : f i = w := by simpa using hiFiber
  have hval := congrArg (fun x : Fin (D + 1) => x.val) hfi
  change dd i = w.val at hval
  refine ⟨aa i, ?_⟩
  intro j hj
  have hiHalf : i ≤ blockLength L i / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    calc
      i * 2 ≤ 2 ^ i * 2 := Nat.mul_le_mul_right 2 (Nat.le_of_lt i.lt_two_pow_self)
      _ ≤ 2 ^ i * L := Nat.mul_le_mul_left (2 ^ i) hL
      _ = blockLength L i := by rfl
  have hx := (hspec i).2.2 j
    (hj.trans_le ((Nat.le_of_lt hki).trans hiHalf))
  rw [hval] at hx
  obtain ⟨J, hJ, hsum⟩ := mem_occurrenceSums.mp hx
  exact ⟨J, Set.subset_univ _, hsum.symm⟩

end Jsp285
