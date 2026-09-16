/- leanprover/lean4:v4.34.0-rc1  mathlib 1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d -/
/-
Comparator challenge module for the JSP-000600 submission (Erdős Problem 732, upper bound).
This module imports only Mathlib and contains the definitions and the target statement with a
`sorry` proof, so that it can be compared mechanically against the solution module
`Proof.Main`, which proves `Erdos732Upper.erdos_732_upper` with the same definitions.
The three definitions are byte-for-byte those of plby/lean-proofs
`src/latest/ErdosProblems/Erdos732.lean` (the existing formalization of Alon's lower bound),
so the upper bound proved here and the lower bound proved there concern the same objects.
-/

import Mathlib

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

/-- **Erdős Problem 732, upper bound.** The number of block-compatible sequences for `n`
(counted as multisets of block sizes) is at most `exp (C √n log n)` for all large `n`. -/
theorem erdos_732_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      {S : Multiset ℕ | BlockCompatible n S}.Finite ∧
        (({S : Multiset ℕ | BlockCompatible n S}.ncard : ℝ) ≤
          Real.exp (C * Real.sqrt n * Real.log n)) := by
  sorry

end Erdos732Upper
