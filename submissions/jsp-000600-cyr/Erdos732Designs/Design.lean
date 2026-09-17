import Mathlib

/-!
# Pairwise balanced designs and block-compatible size multisets

The three definitions `PairwiseBalancedDesign`, `PairwiseBalancedDesign.blockSizes` and
`BlockCompatible` are reproduced verbatim from the existing formalization of Alon's lower
bound for Erdős Problem 732 in plby/lean-proofs (`src/latest/ErdosProblems/Erdos732.lean`,
formal authors Codex and GPT-5.6 Sol, Apache 2.0 license), so that the upper bound proved in
this project is stated for exactly the same objects as the formal lower bound.

A pairwise balanced design on a finite point type `P` is a finite family of blocks (subsets of
`P`) such that every block has at least two points and every pair of distinct points lies in
exactly one block.  A multiset of natural numbers is block-compatible for `n` if it is the
multiset of block sizes of some pairwise balanced design on `Fin n`.

This file also proves the elementary design facts used by the counting argument:
two distinct blocks share at most one point, every block has at most `n` points, and
there are at most `n * n` blocks (each block contains a pair of distinct points and distinct
blocks contain distinct pairs).
-/

open Finset

namespace Erdos732Upper

universe u

/-- A finite pairwise balanced block design: every pair of distinct points is
contained in exactly one block, and every block has at least two points. -/
structure PairwiseBalancedDesign (P : Type u) [Fintype P] where
  Block : Type u
  blockFintype : Fintype Block
  block : Block → Finset P
  two_le_card : ∀ i, 2 ≤ (block i).card
  pair_unique : ∀ ⦃x y : P⦄, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

attribute [instance] PairwiseBalancedDesign.blockFintype

/-- The multiset of block cardinalities of a design. -/
noncomputable def PairwiseBalancedDesign.blockSizes {P : Type u} [Fintype P]
    (D : PairwiseBalancedDesign P) : Multiset ℕ :=
  Finset.univ.val.map fun i ↦ (D.block i).card

/-- A block-size multiset is compatible for `n` if a pairwise balanced design
on `Fin n` has exactly those block sizes. -/
def BlockCompatible (n : ℕ) (sizes : Multiset ℕ) : Prop :=
  ∃ D : PairwiseBalancedDesign (Fin n), D.blockSizes = sizes

namespace PairwiseBalancedDesign

variable {P : Type u} [Fintype P] (D : PairwiseBalancedDesign P)

/-- Two distinct blocks share at most one point. -/
theorem card_inter_le_one [DecidableEq P] {i j : D.Block} (hij : i ≠ j) :
    (D.block i ∩ D.block j).card ≤ 1 := by
  refine Finset.card_le_one.2 fun x hx y hy ↦ ?_
  by_contra hxy
  rw [Finset.mem_inter] at hx hy
  obtain ⟨k, -, hk⟩ := D.pair_unique hxy
  exact hij ((hk i ⟨hx.1, hy.1⟩).trans (hk j ⟨hx.2, hy.2⟩).symm)

/-- Every block is a subset of the point set. -/
theorem card_block_le (i : D.Block) : (D.block i).card ≤ Fintype.card P := by
  exact Finset.card_le_univ _

/-- A design on `n` points has at most `n * n` blocks. -/
theorem card_Block_le : Fintype.card D.Block ≤ Fintype.card P * Fintype.card P := by
  have h : ∀ i : D.Block, ∃ p : P × P, p.1 ≠ p.2 ∧ p.1 ∈ D.block i ∧ p.2 ∈ D.block i := by
    intro i
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (D.two_le_card i)
    exact ⟨(x, y), hxy, hx, hy⟩
  choose f hf using h
  have hinj : Function.Injective f := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := D.pair_unique (hf i).1
    have hi : i = k := hk i ⟨(hf i).2.1, (hf i).2.2⟩
    have hj' := hf j
    rw [← hij] at hj'
    have hj : j = k := hk j ⟨hj'.2.1, hj'.2.2⟩
    exact hi.trans hj.symm
  simpa [Fintype.card_prod] using Fintype.card_le_of_injective f hinj

/-- Every block size lies in `[2, card P]`. -/
theorem mem_blockSizes {x : ℕ} (hx : x ∈ D.blockSizes) : 2 ≤ x ∧ x ≤ Fintype.card P := by
  rw [blockSizes, Multiset.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact ⟨D.two_le_card i, D.card_block_le i⟩

/-- The multiset of block sizes has as many entries as there are blocks. -/
theorem card_blockSizes : Multiset.card D.blockSizes = Fintype.card D.Block := by
  rw [blockSizes, Multiset.card_map, Finset.card_val, Finset.card_univ]

/-- Every multiplicity in the block-size multiset is at most `n * n`. -/
theorem count_blockSizes_le (k : ℕ) :
    D.blockSizes.count k ≤ Fintype.card P * Fintype.card P := by
  have h := Multiset.count_le_card k D.blockSizes
  rw [D.card_blockSizes] at h
  exact h.trans D.card_Block_le

end PairwiseBalancedDesign

end Erdos732Upper
