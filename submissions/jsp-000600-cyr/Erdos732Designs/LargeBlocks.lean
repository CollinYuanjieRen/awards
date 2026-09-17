import Mathlib
import Erdos732Designs.Design

/-!
# Few large blocks

If `T` blocks of a design each have at least `T` points then, because two distinct blocks
share at most one point, their union has at least `T * T - T * (T - 1) / 2 = T * (T + 1) / 2`
points (Alon, remark191 §3: "the size of the union of a set of blocks `A_i`, `i ∈ I`, is at
least `∑ |A_i| - ∑_{i<j} |A_i ∩ A_j|`").  Hence when `T * (T + 1) / 2 > n`, i.e. when
`2 * n < T * T`, fewer than `T` blocks of a design on `n` points have `T` or more points.
-/

open Finset

namespace Erdos732Upper

/-- Bonferroni-type lower bound for the union of a family of large, almost disjoint sets:
if every member has at least `m` elements and two distinct members share at most one
element, then `2 * |⋃ f| + k * (k - 1) ≥ 2 * k * m` where `k` is the number of members. -/
theorem two_mul_card_biUnion_add_ge {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (f : ι → Finset α) (m : ℕ) (hm : ∀ i ∈ s, m ≤ (f i).card)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i ∩ f j).card ≤ 1) :
    2 * (s.card * m) ≤ 2 * (s.biUnion f).card + s.card * (s.card - 1) := by
  classical
  suffices h : 2 * (s.card * m) + s.card ≤ 2 * (s.biUnion f).card + s.card * s.card by
    have h1 : s.card * (s.card - 1) = s.card * s.card - s.card := Nat.mul_sub_one _ _
    omega
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hm' : ∀ i ∈ s, m ≤ (f i).card := fun i hi ↦ hm i (mem_insert_of_mem hi)
    have hinter' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i ∩ f j).card ≤ 1 :=
      fun i hi j hj ↦ hinter i (mem_insert_of_mem hi) j (mem_insert_of_mem hj)
    have ih' := ih hm' hinter'
    have hcap : (f a ∩ s.biUnion f).card ≤ s.card := by
      rw [inter_biUnion]
      refine card_biUnion_le.trans ?_
      calc ∑ i ∈ s, (f a ∩ f i).card ≤ ∑ i ∈ s, 1 :=
            sum_le_sum fun i hi ↦ hinter a (mem_insert_self a s) i (mem_insert_of_mem hi)
              fun h ↦ ha (h ▸ hi)
        _ = s.card := by simp
    have hunion := card_union_add_card_inter (f a) (s.biUnion f)
    have hma := hm a (mem_insert_self a s)
    rw [biUnion_insert, card_insert_of_notMem ha]
    nlinarith

namespace PairwiseBalancedDesign

variable {n : ℕ} (D : PairwiseBalancedDesign (Fin n))

/-- Fewer than `T` blocks have at least `T` points whenever `2 * n < T * T`. -/
theorem card_filter_large_lt (T : ℕ) (hT : 2 * n < T * T) :
    (Finset.univ.filter fun i : D.Block ↦ T ≤ (D.block i).card).card < T := by
  by_contra h
  obtain ⟨t, ht, htcard⟩ := exists_subset_card_eq (not_lt.1 h)
  have h1 := two_mul_card_biUnion_add_ge t D.block T (fun i hi ↦ (mem_filter.1 (ht hi)).2)
    fun i _ j _ hij ↦ D.card_inter_le_one hij
  have h2 : (t.biUnion D.block).card ≤ n := by
    simpa using card_le_univ (t.biUnion D.block)
  rw [htcard] at h1
  have h3 : T * (T - 1) = T * T - T := Nat.mul_sub_one _ _
  omega

/-- The same statement for the multiset of block sizes: fewer than `T` block sizes are `≥ T`. -/
theorem card_filter_blockSizes_lt (T : ℕ) (hT : 2 * n < T * T) :
    Multiset.card (D.blockSizes.filter fun x ↦ T ≤ x) < T := by
  have h := D.card_filter_large_lt T hT
  rw [blockSizes, Multiset.filter_map, Multiset.card_map, ← filter_val, card_val]
  exact h

end PairwiseBalancedDesign

end Erdos732Upper
