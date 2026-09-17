import Mathlib

/-!
# Erdős problem #1020 — definitions for the matching function `f(n; r, k)`

Erdős problem #1020 asks about the *Erdős matching conjecture*: writing `f(n; r, k)` for the
maximal number of edges of an `r`-uniform hypergraph on `n` vertices that contains no set of `k`
pairwise disjoint ("independent") edges, the conjecture is that for all `r ≥ 3`

`f(n; r, k) = max (C(rk - 1, r)) (C(n, r) - C(n - k + 1, r))`.

This module fixes the elementary vocabulary used by the package: `IsUniform`, `HasMatching` and
`f` itself, together with the two basic facts that make `f` transparent — `card_le_f` (every
admissible hypergraph is at most as large as `f`) and `f_le_choose` (`f` never exceeds the total
number of `r`-subsets). A hypergraph on `n` vertices is modelled as a `Finset (Finset (Fin n))`,
so there are only finitely many of them and `f` can be taken to be a `Finset.sup` over the
(classically decidable) family of admissible hypergraphs.

The combinatorial content lives in `Proof.Main`.
-/

namespace Erdos1020

/-- `IsUniform r H` says that the hypergraph `H` is `r`-uniform: every edge has exactly `r`
vertices. -/
def IsUniform {n : ℕ} (r : ℕ) (H : Finset (Finset (Fin n))) : Prop := ∀ e ∈ H, e.card = r

/-- `HasMatching k H` says that `H` contains `k` independent edges: a subfamily `M ⊆ H` of size
`k` whose members are pairwise disjoint. -/
def HasMatching {n : ℕ} (k : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∃ M ⊆ H, M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id

open Classical in
/-- `f n r k` is the `f(n; r, k)` of Erdős problem #1020: the maximal number of edges of an
`r`-uniform hypergraph on `n` vertices containing no `k` independent edges. There are only
finitely many hypergraphs on `Fin n`, so this is the supremum of the cardinalities of those that
are `r`-uniform and free of `k`-matchings. For `k ≥ 1` the empty hypergraph is admissible, so the
`Finset.sup` is over a nonempty family; for `k = 0` every hypergraph has a `0`-matching (the empty
set of edges), the family is empty and `f n r 0 = 0` is the supremum of the empty family. -/
noncomputable def f (n r k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
    (fun H => IsUniform r H ∧ ¬ HasMatching k H)).sup Finset.card

/-- (T5) `f n r k` is an upper bound: every `r`-uniform hypergraph on `n` vertices without `k`
independent edges has at most `f n r k` edges. -/
theorem card_le_f (n r k : ℕ) (H : Finset (Finset (Fin n))) (hH : IsUniform r H)
    (hM : ¬ HasMatching k H) : H.card ≤ f n r k := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hH, hM⟩)

/-- `f n r k` is the *least* such upper bound: `f n r k ≤ m` exactly when every `r`-uniform
matching-free hypergraph on `n` vertices has at most `m` edges. -/
theorem f_le_iff (n r k m : ℕ) :
    f n r k ≤ m ↔
      ∀ H : Finset (Finset (Fin n)), IsUniform r H → ¬ HasMatching k H → H.card ≤ m := by
  classical
  constructor
  · intro h H hH hM
    exact le_trans (card_le_f n r k H hH hM) h
  · intro h
    refine Finset.sup_le ?_
    intro H hH
    obtain ⟨-, h₁, h₂⟩ := Finset.mem_filter.1 hH
    exact h H h₁ h₂

/-- (T4) `f n r k ≤ C(n, r)`: an `r`-uniform hypergraph on `n` vertices is a family of
`r`-element subsets of an `n`-element set, and there are `n.choose r` of those. -/
theorem f_le_choose (n r k : ℕ) : f n r k ≤ n.choose r := by
  classical
  refine (f_le_iff n r k _).2 ?_
  intro H hH _
  have hsub : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r := by
    intro e he
    exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hH e he⟩
  calc H.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard r).card := Finset.card_le_card hsub
    _ = n.choose r := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end Erdos1020
