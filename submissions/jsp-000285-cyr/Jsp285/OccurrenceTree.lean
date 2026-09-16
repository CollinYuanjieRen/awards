import Jsp285.OccurrenceSums
import ErdosProblems.Erdos344

/-! Partition trees of occurrence indices and their actual weighted subset sums. -/

namespace Jsp285


/-- Leafwise properties combine under the pointwise union of two partition
trees at the same depth. -/
lemma allLeaves_zipUnion_of_separate
    {ι : Type*} [DecidableEq ι] {t : ℕ}
    {P Q R : Finset ι → Prop} (A B : Erdos344.PartitionTree ι t)
    (hA : A.AllLeaves P) (hB : B.AllLeaves Q)
    (hcombine : ∀ C D, P C → Q D → R (C ∪ D)) :
    (A.zipUnion B).AllLeaves R := by
  induction A with
  | leaf C =>
      cases B with
      | leaf D => exact hcombine C D hA hB
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          exact ⟨ih₁ B₁ hA.1 hB.1, ih₂ B₂ hA.2 hB.2⟩

/-- The additive carrier obtained by mapping every leaf to its occurrence
subset sums is contained in the subset sums of the whole occurrence carrier. -/
lemma carrier_map_occurrenceSums_subset
    {ι : Type*} [DecidableEq ι] {t : ℕ} (v : ι → ℕ)
    (T : Erdos344.PartitionTree ι t) (hdisj : T.PairwiseDisjoint) :
    (T.mapSumTree (occurrenceSums v)).carrier ⊆ occurrenceSums v T.carrier := by
  induction T with
  | leaf C => exact fun _ hx => hx
  | node A B ihA ihB =>
      rcases hdisj with ⟨hA, hB, hAB⟩
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
      exact add_mem_occurrenceSums hAB (ihA hA ha) (ihB hB hb)

/-- A deep disjoint occurrence tree with large bounded leaf sumsets contains
the progression supplied by the generic sum-tree growth theorem. -/
theorem containsFiniteAP_of_occurrence_tree
    {ι : Type*} [DecidableEq ι] {t K box : ℕ} (v : ι → ℕ)
    (T : Erdos344.PartitionTree ι t) (hK : 2 ≤ K)
    (hdisj : T.PairwiseDisjoint)
    (hcard : T.AllLeaves fun C => K ≤ (occurrenceSums v C).card)
    (hbox : T.AllLeaves fun C => occurrenceSums v C ⊆ Finset.Icc 0 box)
    (hexceed : 2 ^ t * box + 1 < Erdos344.SumTree.growthLower K t) :
    Erdos344.ContainsFiniteAP (occurrenceSums v T.carrier : Set ℕ) (2 * K - 1) := by
  let U := T.mapSumTree (occurrenceSums v)
  have hzeroT : T.AllLeaves fun C => 0 ∈ occurrenceSums v C :=
    hcard.mono fun C _ => zero_mem_occurrenceSums v C
  have hzeroU : U.AllLeaves fun S => 0 ∈ S := by
    exact (Erdos344.PartitionTree.allLeaves_mapSumTree
      (occurrenceSums v) T (fun S => 0 ∈ S)).mpr hzeroT
  have hcardU : U.AllLeaves fun S => K ≤ S.card := by
    exact (Erdos344.PartitionTree.allLeaves_mapSumTree
      (occurrenceSums v) T (fun S => K ≤ S.card)).mpr hcard
  have hboxU : U.AllLeaves fun S => S ⊆ Finset.Icc 0 box := by
    exact (Erdos344.PartitionTree.allLeaves_mapSumTree
      (occurrenceSums v) T (fun S => S ⊆ Finset.Icc 0 box)).mpr hbox
  have hAP := Erdos344.SumTree.containsFiniteAP_of_growth_exceeds_diameter
    hK hzeroU hcardU hboxU hexceed
  exact Erdos344.containsFiniteAP_mono
    (carrier_map_occurrenceSums_subset v T hdisj) hAP

end Jsp285
