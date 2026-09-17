import Erdos732Designs.Design

/-!
# Completing a partial design to a pairwise balanced design

A *partial design* on a finite type `Q` is a finite family `F` of subsets of `Q` (the blocks)
such that every block has at least two points and two distinct blocks meet in at most one
point.  Its *completion* adds to `F` every `2`-element subset of `Q` that is not contained in
a block of `F`; the result is a pairwise balanced design in the sense of
`Erdos732Upper.PairwiseBalancedDesign`.

The multiset of block sizes of the completion is the multiset of sizes of the blocks of `F`
together with one copy of `2` for each uncovered pair.  Consequently, for `s ≠ 2` the
multiplicity of `s` among the block sizes of the completion is exactly the number of blocks
of `F` of size `s`.
-/

namespace Erdos732Lower

open Finset

universe u

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- The 2-subsets of `Q` not contained in any block of `F`. -/
def uncoveredPairs (F : Finset (Finset Q)) : Finset (Finset Q) :=
  (Finset.univ : Finset (Finset Q)).filter fun e => e.card = 2 ∧ ∀ B ∈ F, ¬ e ⊆ B

/-- `F` together with its uncovered pairs. -/
def completion (F : Finset (Finset Q)) : Finset (Finset Q) := F ∪ uncoveredPairs F

/-- A partial design: blocks of size ≥ 2 meeting pairwise in ≤ 1 point. -/
structure IsPartialDesign (F : Finset (Finset Q)) : Prop where
  two_le : ∀ B ∈ F, 2 ≤ B.card
  inter_le : ∀ B ∈ F, ∀ B' ∈ F, B ≠ B' → (B ∩ B').card ≤ 1

/-- Unfolding of membership in `uncoveredPairs`. -/
private theorem mem_uncoveredPairs {F : Finset (Finset Q)} {e : Finset Q} :
    e ∈ uncoveredPairs F ↔ e.card = 2 ∧ ∀ B ∈ F, ¬ e ⊆ B := by
  simp [uncoveredPairs]

/-- A pair `{x, y}` is contained in `B` exactly when both of its points are. -/
private theorem pair_subset_iff {α : Type*} [DecidableEq α] {x y : α} {B : Finset α} :
    ({x, y} : Finset α) ⊆ B ↔ x ∈ B ∧ y ∈ B := by
  simp [Finset.insert_subset_iff]

theorem disjoint_uncoveredPairs (F : Finset (Finset Q)) : Disjoint F (uncoveredPairs F) := by
  rw [Finset.disjoint_left]
  intro B hB hB'
  exact (mem_uncoveredPairs.1 hB').2 B hB Finset.Subset.rfl

/-- The pairwise balanced design obtained by completing a partial design. -/
def completionDesign (F : Finset (Finset Q)) (hF : IsPartialDesign F) :
    Erdos732Upper.PairwiseBalancedDesign Q where
  Block := {B : Finset Q // B ∈ completion F}
  blockFintype := inferInstance
  block := Subtype.val
  two_le_card := by
    rintro ⟨B, hB⟩
    rcases Finset.mem_union.1 hB with h | h
    · exact hF.two_le B h
    · exact (mem_uncoveredPairs.1 h).1.ge
  pair_unique := by
    intro x y hxy
    by_cases hc : ∃ B ∈ F, x ∈ B ∧ y ∈ B
    · obtain ⟨B, hBF, hxB, hyB⟩ := hc
      refine ⟨⟨B, Finset.mem_union_left _ hBF⟩, ⟨hxB, hyB⟩, ?_⟩
      rintro ⟨B', hB'⟩ ⟨hxB', hyB'⟩
      refine Subtype.ext ?_
      rcases Finset.mem_union.1 hB' with h | h
      · by_contra hne
        have hlt : 1 < (B' ∩ B).card :=
          Finset.one_lt_card.2 ⟨x, Finset.mem_inter.2 ⟨hxB', hxB⟩, y,
            Finset.mem_inter.2 ⟨hyB', hyB⟩, hxy⟩
        exact absurd (hF.inter_le B' h B hBF hne) (not_le.2 hlt)
      · obtain ⟨hcard, hsub⟩ := mem_uncoveredPairs.1 h
        have hB'eq : ({x, y} : Finset Q) = B' :=
          Finset.eq_of_subset_of_card_le (pair_subset_iff.2 ⟨hxB', hyB'⟩)
            (by rw [hcard, Finset.card_pair hxy])
        exact absurd (hB'eq ▸ pair_subset_iff.2 ⟨hxB, hyB⟩) (hsub B hBF)
    · have hc' : ∀ B ∈ F, x ∈ B → y ∉ B := fun B hB hx hy => hc ⟨B, hB, hx, hy⟩
      have hmem : ({x, y} : Finset Q) ∈ uncoveredPairs F :=
        mem_uncoveredPairs.2 ⟨Finset.card_pair hxy, fun B hB hsub =>
          hc' B hB (pair_subset_iff.1 hsub).1 (pair_subset_iff.1 hsub).2⟩
      refine ⟨⟨{x, y}, Finset.mem_union_right _ hmem⟩,
        ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩, ?_⟩
      rintro ⟨B', hB'⟩ ⟨hxB', hyB'⟩
      refine Subtype.ext ?_
      rcases Finset.mem_union.1 hB' with h | h
      · exact absurd hyB' (hc' B' h hxB')
      · exact (Finset.eq_of_subset_of_card_le (pair_subset_iff.2 ⟨hxB', hyB'⟩)
          (by rw [(mem_uncoveredPairs.1 h).1, Finset.card_pair hxy])).symm

theorem completionDesign_blockSizes (F : Finset (Finset Q)) (hF : IsPartialDesign F) :
    (completionDesign F hF).blockSizes =
      F.val.map Finset.card + (uncoveredPairs F).val.map Finset.card := by
  have huniv : (Finset.univ : Finset (completionDesign F hF).Block) = (completion F).attach := by
    ext x
    simp only [Finset.mem_univ, true_iff]
    exact Finset.mem_attach _ _
  have hmap := Multiset.map_map (Finset.card (α := Q))
    (Subtype.val (p := fun B : Finset Q => B ∈ completion F)) ((completion F).val.attach)
  rw [Multiset.attach_map_val] at hmap
  have h1 : (completionDesign F hF).blockSizes = (completion F).val.map Finset.card := by
    rw [Erdos732Upper.PairwiseBalancedDesign.blockSizes, huniv, Finset.attach_val]
    exact hmap.symm
  rw [h1, completion, ← Finset.disjUnion_eq_union F _ (disjoint_uncoveredPairs F),
    Finset.disjUnion_val, Multiset.map_add]

theorem count_completionDesign_blockSizes (F : Finset (Finset Q)) (hF : IsPartialDesign F)
    (s : ℕ) (hs : s ≠ 2) :
    Multiset.count s (completionDesign F hF).blockSizes =
      Multiset.count s (F.val.map Finset.card) := by
  have hzero : Multiset.count s ((uncoveredPairs F).val.map Finset.card) = 0 := by
    rw [Multiset.count_eq_zero]
    intro h
    obtain ⟨e, he, hse⟩ := Multiset.mem_map.1 h
    exact hs (hse ▸ (mem_uncoveredPairs.1 he).1)
  rw [completionDesign_blockSizes, Multiset.count_add, hzero, Nat.add_zero]

end Erdos732Lower
