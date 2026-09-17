import Mathlib

/-!
# Erdős problem #963: dissociated subsets — definitions and the representation lemma

This module fixes the two definitions used by the package and proves the combinatorial
heart of Erdős's greedy bound.

A finite set `B ⊆ ℝ` is *dissociated* when the subset sums `∑ b ∈ S, b` are pairwise
distinct as `S` ranges over subsets of `B`, and `f n` is the largest `k` such that every
`n`-element set of reals contains a dissociated subset of size at least `k`.

The key lemma `Erdos963.exists_repr_of_maximal` says that if `B ⊆ A` is dissociated of
*maximal* size among the dissociated subsets of `A`, then every `a ∈ A` is a signed sum
`a = ∑ b ∈ B, ε b * b` with coefficients `ε b ∈ {-1, 0, 1}`.  Indeed, for `a ∉ B` the set
`insert a B` is too big to be dissociated, so two distinct subsets of `insert a B` have
equal sums; `a` lies in exactly one of them (else erasing `a` from both would contradict
the dissociation of `B`), and cancelling the rest expresses `a` as such a signed sum.
-/

namespace Erdos963

/-- A finite set `B` of reals is **dissociated** when distinct subsets of `B` have
distinct sums: `∑ x ∈ S, x = ∑ x ∈ T, x` forces `S = T` for `S, T ⊆ B`. -/
def Dissociated (B : Finset ℝ) : Prop :=
  ∀ S ⊆ B, ∀ T ⊆ B, ∑ x ∈ S, x = ∑ x ∈ T, x → S = T

/-- `f n` is the largest `k` such that **every** set of `n` reals contains a dissociated
subset of size at least `k`.  This is the `f` of Erdős problem #963.  The defining set
contains `0` and is bounded above by `n`, so the supremum is attained (see
`Erdos963.f_le` and `Erdos963.exists_dissociated_subset_f`). -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, Dissociated B ∧ k ≤ B.card}

/-- The empty set is dissociated: the only subset of `∅` is `∅`. -/
theorem dissociated_empty : Dissociated ∅ := by
  intro S hS T hT _
  rw [Finset.subset_empty] at hS hT
  rw [hS, hT]

/-- A subset of a dissociated set is dissociated. -/
theorem Dissociated.mono {B C : Finset ℝ} (h : Dissociated C) (hBC : B ⊆ C) :
    Dissociated B := by
  intro S hS T hT hsum
  exact h S (hS.trans hBC) T (hT.trans hBC) hsum

/-- **Representation lemma.**  If `B ⊆ A` is dissociated and of maximal cardinality among
the dissociated subsets of `A`, then every `a ∈ A` is a signed sum of the elements of `B`
with coefficients in `{-1, 0, 1}`. -/
theorem exists_repr_of_maximal {A B : Finset ℝ} (hBA : B ⊆ A) (hB : Dissociated B)
    (hmax : ∀ C ⊆ A, Dissociated C → C.card ≤ B.card) (a : ℝ) (ha : a ∈ A) :
    ∃ ε : ℝ → ℤ, (∀ b ∈ B, ε b = -1 ∨ ε b = 0 ∨ ε b = 1) ∧ a = ∑ b ∈ B, (ε b : ℝ) * b := by
  classical
  by_cases haB : a ∈ B
  · -- `a ∈ B`: take the indicator of `{a}`.
    refine ⟨fun b => if b = a then 1 else 0, ?_, ?_⟩
    · intro b _
      dsimp only
      split_ifs <;> simp
    · simp [haB]
  · -- `a ∉ B`: `insert a B` is strictly bigger than `B`, hence not dissociated.
    have hsub : insert a B ⊆ A := Finset.insert_subset ha hBA
    have hcard : B.card < (insert a B).card := by
      rw [Finset.card_insert_of_notMem haB]
      omega
    have hnd : ¬ Dissociated (insert a B) := by
      intro h
      have := hmax _ hsub h
      omega
    -- Two distinct subsets of `insert a B` with equal sums.
    simp only [Dissociated, not_forall] at hnd
    obtain ⟨S, hS, T, hT, hsum, hne⟩ := hnd
    -- Subsets of `insert a B` avoiding `a` are subsets of `B` …
    have keyNot : ∀ U : Finset ℝ, U ⊆ insert a B → a ∉ U → U ⊆ B := by
      intro U hU haU x hx
      rcases Finset.mem_insert.1 (hU hx) with h | h
      · exact absurd (h ▸ hx) haU
      · exact h
    -- … and erasing `a` always lands inside `B`.
    have keyErase : ∀ U : Finset ℝ, U ⊆ insert a B → U.erase a ⊆ B := by
      intro U hU x hx
      have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      rcases Finset.mem_insert.1 (hU (Finset.mem_of_mem_erase hx)) with h | h
      · exact absurd h hxa
      · exact h
    -- The asymmetric case, used twice (with `S`, `T` swapped the second time).
    have main : ∀ S T : Finset ℝ, S ⊆ insert a B → T ⊆ insert a B → a ∈ S → a ∉ T →
        ∑ x ∈ S, x = ∑ x ∈ T, x →
        ∃ ε : ℝ → ℤ, (∀ b ∈ B, ε b = -1 ∨ ε b = 0 ∨ ε b = 1) ∧
          a = ∑ b ∈ B, (ε b : ℝ) * b := by
      intro S T hS hT haS haT hsum
      have hSB : S.erase a ⊆ B := keyErase S hS
      have hTB : T ⊆ B := keyNot T hT haT
      -- `a + ∑ (S.erase a) = ∑ S = ∑ T`, so `a = ∑ T - ∑ (S.erase a)`.
      have hsplit : a + ∑ x ∈ S.erase a, x = ∑ x ∈ S, x :=
        Finset.add_sum_erase S (fun x => x) haS
      have harep : a = (∑ x ∈ T, x) - ∑ x ∈ S.erase a, x := by
        rw [← hsum, ← hsplit]; ring
      refine ⟨fun b => (if b ∈ T then 1 else 0) - (if b ∈ S.erase a then 1 else 0), ?_, ?_⟩
      · intro b _
        dsimp only
        split_ifs <;> norm_num
      · -- Expand the coefficient at a single `b ∈ B`.
        have expand : ∀ b ∈ B,
            (((if b ∈ T then (1 : ℤ) else 0) - (if b ∈ S.erase a then (1 : ℤ) else 0) : ℤ) : ℝ)
              * b
            = (if b ∈ T then b else 0) - (if b ∈ S.erase a then b else 0) := by
          intro b _
          split_ifs <;> push_cast <;> ring
        dsimp only
        calc a = (∑ x ∈ T, x) - ∑ x ∈ S.erase a, x := harep
          _ = ∑ b ∈ B, ((if b ∈ T then b else 0) - (if b ∈ S.erase a then b else 0)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
                Finset.inter_eq_right.2 hTB, Finset.inter_eq_right.2 hSB]
          _ = ∑ b ∈ B,
                (((if b ∈ T then (1 : ℤ) else 0) - (if b ∈ S.erase a then (1 : ℤ) else 0) : ℤ) : ℝ)
                  * b := (Finset.sum_congr rfl expand).symm
    by_cases haS : a ∈ S <;> by_cases haT : a ∈ T
    · -- `a` in both: erase it from both and contradict the dissociation of `B`.
      exfalso
      have h1 : a + ∑ x ∈ S.erase a, x = ∑ x ∈ S, x :=
        Finset.add_sum_erase S (fun x => x) haS
      have h2 : a + ∑ x ∈ T.erase a, x = ∑ x ∈ T, x :=
        Finset.add_sum_erase T (fun x => x) haT
      have heq : ∑ x ∈ S.erase a, x = ∑ x ∈ T.erase a, x := by
        have : a + ∑ x ∈ S.erase a, x = a + ∑ x ∈ T.erase a, x := by rw [h1, h2, hsum]
        linarith
      have := hB _ (keyErase S hS) _ (keyErase T hT) heq
      exact hne (by rw [← Finset.insert_erase haS, ← Finset.insert_erase haT, this])
    · exact main S T hS hT haS haT hsum
    · exact main T S hT hS haT haS hsum.symm
    · -- `a` in neither: `S` and `T` are subsets of `B` with equal sums.
      exact absurd (hB _ (keyNot S hS haS) _ (keyNot T hT haT) hsum) hne

end Erdos963
