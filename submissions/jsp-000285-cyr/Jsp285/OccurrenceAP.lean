import Jsp285.OccurrenceTree
import Jsp285.LeafMassBounds
import Jsp285.FiniteConstants

/-! The existing depth-48 growth theorem applied to balanced occurrence leaves. -/

namespace Jsp285

open Erdos344

/-- Balanced disjoint occurrence leaves yield an AP at the original target length. -/
theorem containsAP_of_balanced_occurrence_tree {ι : Type*} [DecidableEq ι]
    (v : ι → ℕ) (S : Finset ι) (N n : ℕ) (hn : 0 < n)
    (hbox : ∀ i ∈ S, 0 < v i ∧ v i ≤ N)
    (hmass : 39999 * partitionMass * n ≤ ∑ i ∈ S, v i)
    (T : PartitionTree ι 49) (hcarrier : T.carrier = S)
    (hdisj : T.PairwiseDisjoint)
    (hleaf : T.AllLeaves fun C ↦ C ⊆ S ∧
      (∀ e : ℕ, 1 < e → e ≤ N → e - 1 ≤ (C.filter fun i ↦ ¬e ∣ v i).card) ∧
      89 ^ 49 * (∑ i ∈ S, v i) ≤ 2 * partitionMass * (∑ i ∈ C, v i) ∧
      partitionMass * (∑ i ∈ C, v i) ≤ 2 * 111 ^ 49 * (∑ i ∈ S, v i)) :
    ContainsFiniteAP (occurrenceSums v S : Set ℕ) n := by
  let W := ∑ i ∈ S, v i
  let q := W / partitionMass
  let K := 89 ^ 49 * (q / 16)
  let box := 40 * 111 ^ 49 * (q + 1)
  have hH : 0 < partitionMass := by norm_num [partitionMass]
  have hq : 39999 * n ≤ q := by
    apply (Nat.le_div_iff_mul_le hH).mpr
    simpa [W, mul_assoc, mul_comm, mul_left_comm] using hmass
  have hq32 : 32 ≤ q := by omega
  have hquot : 2 * n ≤ q / 16 := by omega
  have ha : 1 ≤ 89 ^ 49 := one_le_pow₀ (by omega)
  have hKlarge : 2 * n ≤ K := hquot.trans (Nat.le_mul_of_pos_left _ ha)
  have hK : 2 ≤ K := by omega
  cases T with
  | node A B =>
    have hA := hleaf.1.and (PartitionTree.allLeaves_subset_carrier A)
    have hB := hleaf.2.and (PartitionTree.allLeaves_subset_carrier B)
    have hpaired : (PartitionTree.zipUnion A B).AllLeaves fun C ↦
        K ≤ (occurrenceSums v C).card ∧
          occurrenceSums v C ⊆ Finset.Icc 0 box := by
      apply allLeaves_zipUnion_of_separate A B hA hB
      intro C P hC hP
      have hCP : Disjoint C P := hdisj.2.2.mono hC.2 hP.2
      have hpairmass : partitionMass * ((∑ i ∈ C, v i) + ∑ i ∈ P, v i) ≤
          4 * 111 ^ 49 * W := by
        have hCmass := hC.1.2.2.2
        have hPmass := hP.1.2.2.2
        dsimp [W]
        nlinarith
      exact pair_leaf_bounds v C P N W partitionMass (89 ^ 49) (111 ^ 49)
        hH hCP (fun i hi ↦ hbox i (hP.1.1 hi)) hC.1.2.1
        hP.1.2.2.1 hpairmass
    have hzipdisj := PartitionTree.pairwiseDisjoint_zipUnion
      hdisj.1 hdisj.2.1 hdisj.2.2
    have hAP := containsFiniteAP_of_occurrence_tree v (PartitionTree.zipUnion A B)
      hK hzipdisj (hpaired.mono fun C h ↦ h.1) (hpaired.mono fun C h ↦ h.2)
      (depth_fortyEight_growth hq32)
    have hzipcarrier : (PartitionTree.zipUnion A B).carrier = S := by
      rw [PartitionTree.carrier_zipUnion]
      exact hcarrier
    rw [hzipcarrier] at hAP
    obtain ⟨a, d, hd, hterms⟩ := hAP
    refine ⟨a, d, hd, ?_⟩
    intro i hi
    exact hterms i (by omega)

end Jsp285
