import Jsp285.InfiniteSums
import ErdosProblems.Erdos344

/-! Residue stabilization with finite supports in occurrence indices. -/

namespace Jsp285

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

private noncomputable def occurrenceResidues (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] : Finset (ZMod d) :=
  Finset.univ.filter fun z =>
    ∃ I : Finset ℕ, (∑ i ∈ I, (y i : ZMod d)) = z

private lemma mem_occurrenceResidues_iff {y : ℕ → ℕ} {d : ℕ} [NeZero d]
    {z : ZMod d} :
    z ∈ occurrenceResidues y d ↔
      ∃ I : Finset ℕ, (∑ i ∈ I, (y i : ZMod d)) = z := by
  simp [occurrenceResidues]

private noncomputable def occurrenceResidueWitness (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] (z : occurrenceResidues y d) : Finset ℕ :=
  Classical.choose (mem_occurrenceResidues_iff.mp z.property)

private lemma occurrenceResidueWitness_spec (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] (z : occurrenceResidues y d) :
    (∑ i ∈ occurrenceResidueWitness y d z, (y i : ZMod d)) = z :=
  Classical.choose_spec (mem_occurrenceResidues_iff.mp z.property)

private noncomputable def occurrenceResidueSupport (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] : Finset ℕ :=
  (occurrenceResidues y d).attach.biUnion (occurrenceResidueWitness y d)

private lemma witness_subset_occurrenceResidueSupport (y : ℕ → ℕ) (d : ℕ)
    [NeZero d] (z : occurrenceResidues y d) :
    occurrenceResidueWitness y d z ⊆ occurrenceResidueSupport y d := by
  intro i hi
  rw [occurrenceResidueSupport, Finset.mem_biUnion]
  exact ⟨z, Finset.mem_attach _ _, hi⟩

/-- Modulo a positive `d`, all sufficiently late occurrence weights are
divisible by some `q ∣ d`, while the initial occurrences represent every
multiple of `q` modulo `d`. -/
theorem exists_occurrence_residue_stabilization (y : ℕ → ℕ)
    {d : ℕ} (hd : 0 < d) :
    ∃ q : ℕ, 0 < q ∧ q ∣ d ∧ ∃ s : ℕ,
      (∀ j, s ≤ j → q ∣ y j) ∧
      (∀ i < d / q, ∃ u ∈ occurrenceSums y (Finset.range s),
        (u : ZMod d) = (i * q : ZMod d)) := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let R := occurrenceResidues y d
  let K := AddAction.stabilizer (ZMod d) R
  obtain ⟨q, hqpos, hqd, hKdiv, hmultK⟩ :=
    Erdos344.exists_generator_modulus hd K
  let s := (occurrenceResidueSupport y d).sup id + 1
  refine ⟨q, hqpos, hqd, s, ?_, ?_⟩
  · intro j hj
    have hjlarge : (occurrenceResidueSupport y d).sup id < j := by
      simpa [s] using hj
    have hjK : (y j : ZMod d) ∈ K := by
      rw [AddAction.mem_stabilizer_finset']
      intro z hz
      let z' : occurrenceResidues y d := ⟨z, hz⟩
      let I := occurrenceResidueWitness y d z'
      have hjI : j ∉ I := by
        intro hjI
        have hjsupp : j ∈ occurrenceResidueSupport y d :=
          witness_subset_occurrenceResidueSupport y d z' hjI
        have hjle := Finset.le_sup (f := id) hjsupp
        exact (not_le_of_gt hjlarge) (by simpa using hjle)
      rw [mem_occurrenceResidues_iff]
      refine ⟨insert j I, ?_⟩
      rw [Finset.sum_insert hjI]
      change (y j : ZMod d) + (∑ i ∈ I, (y i : ZMod d)) = _
      rw [occurrenceResidueWitness_spec y d z']
      rfl
    have hqmod : q ∣ (y j : ZMod d).val := hKdiv _ hjK
    have hqrem : q ∣ y j % d := by
      simpa [ZMod.val_natCast] using hqmod
    have hqdpart : q ∣ d * (y j / d) := dvd_mul_of_dvd_left hqd _
    rw [← Nat.mod_add_div (y j) d]
    exact dvd_add hqrem hqdpart
  · intro i hi
    have hiK : (i * q : ZMod d) ∈ K := hmultK i
    have hzero : (0 : ZMod d) ∈ R := by
      rw [mem_occurrenceResidues_iff]
      exact ⟨∅, by simp⟩
    have hiR : (i * q : ZMod d) ∈ R := by
      have := (AddAction.mem_stabilizer_finset'.mp hiK) hzero
      simpa using this
    let z : occurrenceResidues y d := ⟨(i * q : ZMod d), hiR⟩
    let I := occurrenceResidueWitness y d z
    have hIrange : I ⊆ Finset.range s := by
      intro j hjI
      have hjsupp : j ∈ occurrenceResidueSupport y d :=
        witness_subset_occurrenceResidueSupport y d z hjI
      have hjle := Finset.le_sup (f := id) hjsupp
      rw [Finset.mem_range]
      simpa [s] using Nat.lt_succ_of_le (by simpa using hjle)
    refine ⟨∑ j ∈ I, y j, ?_, ?_⟩
    · exact mem_occurrenceSums.mpr ⟨I, hIrange, rfl⟩
    · simpa [I, z] using occurrenceResidueWitness_spec y d z

end Jsp285
