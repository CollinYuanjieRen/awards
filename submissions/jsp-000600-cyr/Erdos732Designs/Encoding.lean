import Mathlib
import Erdos732Designs.Design
import Erdos732Designs.LargeBlocks

/-!
# Counting block-compatible multisets

A block-compatible multiset `S` for `n` is determined by

* the multiplicities of the sizes `0, …, T - 1` in `S`, each at most `n * n`
  (`PairwiseBalancedDesign.count_blockSizes_le`), and
* the sub-multiset of sizes `≥ T`, which has fewer than `T` entries
  (`PairwiseBalancedDesign.card_filter_blockSizes_lt`) all of which are `≤ n`.

The first datum ranges over `Fin T → Fin (n * n + 1)`; the second over multisets of
cardinality `k < T` bounded by `k • Multiset.range (n + 1)`, of which there are
`(k * (n + 1)).choose k ≤ (T * (n + 1) + 1) ^ T`.  Hence the set of block-compatible
multisets for `n` is finite with at most `explicitBound n T` elements.
-/

open Finset

namespace Erdos732Upper

/-- The explicit counting bound `(n² + 1)^T · T · (T(n+1) + 1)^T`. -/
def explicitBound (n T : ℕ) : ℕ :=
  (n * n + 1) ^ T * (T * (T * (n + 1) + 1) ^ T)

/-- The candidates for the "large part" of a block-size multiset: multisets of cardinality
`k < T` bounded by `k • Multiset.range (n + 1)`. -/
private def largeParts (n T : ℕ) : Finset (Multiset ℕ) :=
  (Finset.range T).biUnion fun k ↦
    (Multiset.powersetCard k (k • Multiset.range (n + 1))).toFinset

/-- There are at most `T * (T * (n + 1) + 1) ^ T` candidate large parts. -/
private theorem card_largeParts_le (n T : ℕ) :
    (largeParts n T).card ≤ T * (T * (n + 1) + 1) ^ T := by
  refine Finset.card_biUnion_le.trans ?_
  have h : ∀ k ∈ Finset.range T,
      (Multiset.powersetCard k (k • Multiset.range (n + 1))).toFinset.card ≤
        (T * (n + 1) + 1) ^ T := by
    intro k hk
    rw [Finset.mem_range] at hk
    refine (Multiset.toFinset_card_le _).trans ?_
    rw [Multiset.card_powersetCard, Multiset.card_nsmul, Multiset.card_range]
    refine (Nat.choose_le_pow _ _).trans ?_
    calc (k * (n + 1)) ^ k ≤ (T * (n + 1) + 1) ^ k := Nat.pow_le_pow_left (by nlinarith) k
      _ ≤ (T * (n + 1) + 1) ^ T := Nat.pow_le_pow_right (by omega) hk.le
  calc ∑ k ∈ Finset.range T,
        (Multiset.powersetCard k (k • Multiset.range (n + 1))).toFinset.card
      ≤ ∑ k ∈ Finset.range T, (T * (n + 1) + 1) ^ T := Finset.sum_le_sum h
    _ = T * (T * (n + 1) + 1) ^ T := by simp

/-- Encode a multiset by the multiplicities of `0, …, T - 1` (clamped at `n * n`) together with
its sub-multiset of entries `≥ T`. -/
private def encode (n T : ℕ) (S : Multiset ℕ) : (Fin T → Fin (n * n + 1)) × Multiset ℕ :=
  (fun k ↦ ⟨min (S.count (k : ℕ)) (n * n), by omega⟩, S.filter fun x ↦ T ≤ x)

/-- The encoding of a block-compatible multiset lands in `univ ×ˢ largeParts n T`. -/
private theorem encode_mem (n T : ℕ) (hT : 2 * n < T * T) {S : Multiset ℕ}
    (hS : BlockCompatible n S) :
    encode n T S ∈ (Set.univ ×ˢ (largeParts n T : Set (Multiset ℕ)) :
      Set ((Fin T → Fin (n * n + 1)) × Multiset ℕ)) := by
  obtain ⟨D, rfl⟩ := hS
  simp only [encode, Set.mem_prod, Set.mem_univ, true_and, Finset.mem_coe, largeParts,
    Finset.mem_biUnion, Finset.mem_range, Multiset.mem_toFinset, Multiset.mem_powersetCard]
  refine ⟨Multiset.card (D.blockSizes.filter fun x ↦ T ≤ x), D.card_filter_blockSizes_lt T hT,
    ?_, rfl⟩
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul]
  by_cases ha : a ∈ Multiset.range (n + 1)
  · rw [Multiset.count_eq_one_of_mem (Multiset.nodup_range _) ha, mul_one]
    exact Multiset.count_le_card _ _
  · rw [Multiset.count_eq_zero_of_notMem ha, mul_zero, Nat.le_zero, Multiset.count_eq_zero]
    intro h
    have hle := (D.mem_blockSizes (Multiset.mem_of_mem_filter h)).2
    rw [Fintype.card_fin] at hle
    exact ha (Multiset.mem_range.2 (by omega))

/-- The encoding is injective on block-compatible multisets. -/
private theorem encode_injOn (n T : ℕ) :
    Set.InjOn (encode n T) {S : Multiset ℕ | BlockCompatible n S} := by
  rintro S ⟨D, rfl⟩ S' ⟨D', rfl⟩ h
  simp only [encode, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  ext a
  by_cases ha : a < T
  · have h3 := congrArg (fun f ↦ ((f ⟨a, ha⟩ : Fin (n * n + 1)) : ℕ)) h1
    simp only at h3
    have hD := D.count_blockSizes_le a
    have hD' := D'.count_blockSizes_le a
    rw [Fintype.card_fin] at hD hD'
    rwa [min_eq_left hD, min_eq_left hD'] at h3
  · have h3 := congrArg (Multiset.count a) h2
    rwa [Multiset.count_filter_of_pos (by omega), Multiset.count_filter_of_pos (by omega)] at h3

/-- The set of block-compatible multisets for `n` is finite, and has at most
`explicitBound n T` elements whenever `2 * n < T * T`. -/
theorem blockCompatible_finite_and_ncard_le (n T : ℕ) (hT : 2 * n < T * T) :
    {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
      {S : Multiset ℕ | BlockCompatible n S}.ncard ≤ explicitBound n T := by
  have hfin : (Set.univ ×ˢ (largeParts n T : Set (Multiset ℕ)) :
      Set ((Fin T → Fin (n * n + 1)) × Multiset ℕ)).Finite :=
    Set.finite_univ.prod (Finset.finite_toSet _)
  have hmaps : ∀ S ∈ {S : Multiset ℕ | BlockCompatible n S},
      encode n T S ∈ (Set.univ ×ˢ (largeParts n T : Set (Multiset ℕ)) :
        Set ((Fin T → Fin (n * n + 1)) × Multiset ℕ)) :=
    fun _ hS ↦ encode_mem n T hT hS
  refine ⟨?_, ?_⟩
  · exact Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 hmaps))
      (encode_injOn n T)
  · refine (Set.ncard_le_ncard_of_injOn (encode n T) hmaps (encode_injOn n T) hfin).trans ?_
    rw [Set.ncard_prod, Set.ncard_univ, Set.ncard_coe_finset, Nat.card_fun,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin]
    exact Nat.mul_le_mul_left _ (card_largeParts_le n T)

end Erdos732Upper
