import Mathlib

/-!
# Triangle packings and covers: definitions (Erdős problem #167, Tuza's conjecture)

This module fixes the vocabulary used for the scoped component of Erdős problem #167
(Tuza's conjecture) that this package formalises: the *trivial* bound `τ(G) ≤ 3ν(G)`.

A *triangle* of a `SimpleGraph V` is a three-element clique `T : Finset V`; its edge set
`edgesOf T` consists of the three non-diagonal elements of `T.sym2`.  A *packing* is a family
of triangles with pairwise disjoint edge sets, and `packingNumber G = ν(G)` is the largest size
of such a family.  A *cover* is a finset `D` of unordered pairs whose deletion leaves `G`
triangle-free, and `coverNumber G = τ(G)` is the least size of such a `D`.

Besides the six frozen definitions this file contains the elementary lemmas that make them
transparent: membership characterisations for `triangles` and `edgesOf`, the bound
`(edgesOf T).card ≤ 3` for a three-element `T`, and the fact that `ν` is attained by some packing
(`card_le_packingNumber`, `exists_packing_card_eq`) while `τ` is attained by some cover
(`coverNumber_le_card`, `exists_isCover_card_eq`).

The main inequality itself is proved in `Proof.Main`.
-/

namespace Erdos167

open Finset

open Classical in
/-- `triangles G` is the finset of triangles of `G`: the three-element subsets of the vertex
type that are cliques of `G`.  Classical decidability is used for the filter. -/
noncomputable def triangles {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Finset V) := ((Finset.univ : Finset V).powersetCard 3).filter (fun T => G.IsClique (T : Set V))

/-- `edgesOf T` is the set of unordered pairs of distinct elements of `T`, i.e. the edges spanned
by `T`.  For a three-element `T` these are exactly the three edges of the triangle `T`. -/
def edgesOf {V : Type*} [DecidableEq V] (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

/-- `IsPacking G F` says that `F` is a family of triangles of `G` whose edge sets are pairwise
disjoint, i.e. a family of pairwise edge-disjoint triangles. -/
def IsPacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (F : Finset (Finset V)) : Prop := F ⊆ triangles G ∧ (F : Set (Finset V)).PairwiseDisjoint edgesOf

open Classical in
/-- `packingNumber G` is the triangle packing number `ν(G)`: the largest size of a family of
pairwise edge-disjoint triangles of `G`.  Classical decidability is used for the filter. -/
noncomputable def packingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ := ((Finset.univ : Finset (Finset (Finset V))).filter (fun F => IsPacking G F)).sup Finset.card

/-- `IsCover G D` says that deleting the unordered pairs in `D` from `G` leaves a triangle-free
graph. -/
def IsCover {V : Type*} (G : SimpleGraph V) (D : Finset (Sym2 V)) : Prop := (G.deleteEdges (D : Set (Sym2 V))).CliqueFree 3

/-- `coverNumber G` is the triangle cover number `τ(G)`: the least number of edges whose deletion
makes `G` triangle-free. -/
noncomputable def coverNumber {V : Type*} (G : SimpleGraph V) : ℕ := sInf {m : ℕ | ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = m}

/-- Membership in `triangles G`: a finset is a triangle iff it has three elements and is a
clique. -/
theorem mem_triangles {V : Type*} [Fintype V] {G : SimpleGraph V} {T : Finset V} :
    T ∈ triangles G ↔ T.card = 3 ∧ G.IsClique (T : Set V) := by
  classical
  simp [triangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ]

/-- Membership in `edgesOf T`: an unordered pair is an edge of `T` iff both of its endpoints lie
in `T` and it is not a loop. -/
theorem mem_edgesOf {V : Type*} [DecidableEq V] {T : Finset V} {e : Sym2 V} :
    e ∈ edgesOf T ↔ (∀ x ∈ e, x ∈ T) ∧ ¬ e.IsDiag := by
  simp [edgesOf, Finset.mem_filter, Finset.mem_sym2_iff]

/-- A three-element finset spans at most three edges. -/
theorem card_edgesOf_le {V : Type*} [DecidableEq V] (T : Finset V) (hT : T.card = 3) :
    (edgesOf T).card ≤ 3 := by
  have hsum : (T.sym2.filter Sym2.IsDiag).card + (edgesOf T).card = T.sym2.card :=
    Finset.card_filter_add_card_filter_not (s := T.sym2) Sym2.IsDiag
  have hcard : T.sym2.card = 6 := by rw [Finset.card_sym2, hT]; rfl
  -- The diagonal part of `T.sym2` contains the `3` loops at the vertices of `T`.
  have hdiag : 3 ≤ (T.sym2.filter Sym2.IsDiag).card := by
    have hsub : T.image Sym2.diag ⊆ T.sym2.filter Sym2.IsDiag := by
      intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
      refine Finset.mem_filter.2 ⟨?_, Sym2.diag_isDiag a⟩
      show s(a, a) ∈ T.sym2
      exact Finset.mk_mem_sym2_iff.2 ⟨ha, ha⟩
    have hle := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ Sym2.diag_injective, hT] at hle
  omega

/-- T6: every packing has at most `ν(G)` members. -/
theorem card_le_packingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (F : Finset (Finset V)) (h : IsPacking G F) : F.card ≤ packingNumber G := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

/-- The packing number is attained: some packing has exactly `ν(G)` members. -/
theorem exists_packing_card_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ F : Finset (Finset V), IsPacking G F ∧ F.card = packingNumber G := by
  classical
  have hempty : IsPacking G (∅ : Finset (Finset V)) := by
    refine ⟨Finset.empty_subset _, ?_⟩
    rw [Finset.coe_empty]
    exact Set.pairwiseDisjoint_empty
  obtain ⟨F, hF, hsup⟩ :=
    Finset.exists_mem_eq_sup
      ((Finset.univ : Finset (Finset (Finset V))).filter (fun F => IsPacking G F))
      ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, hempty⟩⟩ Finset.card
  exact ⟨F, (Finset.mem_filter.1 hF).2, hsup.symm⟩

/-- T4: the cover number is at most the size of any cover. -/
theorem coverNumber_le_card {V : Type*} (G : SimpleGraph V) (D : Finset (Sym2 V)) (h : IsCover G D) : coverNumber G ≤ D.card :=
  Nat.sInf_le ⟨D, h, rfl⟩

/-- T5: the cover number is attained: some cover has exactly `τ(G)` edges.  The whole (finite)
set of unordered pairs is a cover, so the infimum is over a nonempty set. -/
theorem exists_isCover_card_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = coverNumber G := by
  have hcov : IsCover G (Finset.univ : Finset (Sym2 V)) := by
    show (G.deleteEdges ((Finset.univ : Finset (Sym2 V)) : Set (Sym2 V))).CliqueFree 3
    rw [Finset.coe_univ, SimpleGraph.deleteEdges_univ]
    exact SimpleGraph.cliqueFree_bot (by norm_num)
  have hne : {m : ℕ | ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = m}.Nonempty :=
    ⟨(Finset.univ : Finset (Sym2 V)).card, (Finset.univ : Finset (Sym2 V)), hcov, rfl⟩
  exact Nat.sInf_mem hne

end Erdos167
