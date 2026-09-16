import Mathlib
import Proof.Design

/-!
# A non-vacuity witness: the design of all pairs

This file exhibits an explicit pairwise balanced design on `Fin n` for every `n`, namely the
trivial design whose blocks are all `2`-element subsets of `Fin n`.  Every pair of distinct points
lies in exactly one such block (the block `{x, y}` itself), so this is a
`PairwiseBalancedDesign (Fin n)` in the sense of `MerLeanExperiment.Design`.  Its block-size
multiset is `Multiset.replicate (n.choose 2) 2`, which shows that `BlockCompatible n S` is
satisfiable for every `n` and hence that the notion of block-compatible size multiset is not
vacuous.
-/

open Finset

namespace Erdos732Upper

/-- The trivial pairwise balanced design on `Fin n` whose blocks are all `2`-element subsets. -/
def allPairsDesign (n : ℕ) : PairwiseBalancedDesign (Fin n) where
  Block := {s : Finset (Fin n) // s.card = 2}
  blockFintype := inferInstance
  block := Subtype.val
  two_le_card i := i.property.ge
  pair_unique x y hxy := by
    refine ⟨⟨{x, y}, Finset.card_pair hxy⟩, ⟨by simp, by simp⟩, ?_⟩
    rintro ⟨s, hs⟩ ⟨hxs, hys⟩
    apply Subtype.ext
    have hsub : ({x, y} : Finset (Fin n)) ⊆ s := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hxs
      · rw [Finset.mem_singleton] at hz
        exact hz ▸ hys
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hs, Finset.card_pair hxy])).symm

/-- The block sizes of `allPairsDesign n` are `n.choose 2` copies of `2`. -/
theorem allPairsDesign_blockSizes (n : ℕ) :
    (allPairsDesign n).blockSizes = Multiset.replicate (n.choose 2) 2 := by
  refine Multiset.eq_replicate.2 ⟨?_, ?_⟩
  · rw [PairwiseBalancedDesign.blockSizes, Multiset.card_map, Finset.card_val, Finset.card_univ]
    exact (Fintype.card_finset_len (α := Fin n) 2).trans (by rw [Fintype.card_fin])
  · intro b hb
    rw [PairwiseBalancedDesign.blockSizes, Multiset.mem_map] at hb
    obtain ⟨i, -, rfl⟩ := hb
    exact i.property

/-- The multiset of `n.choose 2` copies of `2` is block-compatible for `n`. -/
theorem blockCompatible_replicate_two (n : ℕ) :
    BlockCompatible n (Multiset.replicate (n.choose 2) 2) :=
  ⟨allPairsDesign n, allPairsDesign_blockSizes n⟩

/-- For every `n` there is at least one block-compatible size multiset. -/
theorem exists_blockCompatible (n : ℕ) : ∃ S : Multiset ℕ, BlockCompatible n S :=
  ⟨_, blockCompatible_replicate_two n⟩

end Erdos732Upper
