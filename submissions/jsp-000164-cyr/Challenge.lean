/-
Comparator-style challenge module for JSP-000164 / Erdős Problem #167 (scoped component).

This file is intentionally self-contained: it depends on Mathlib only and states the root results
of the `Proof` library with `sorry`, so the statements can be compared mechanically with those
proved there (the definitions below are the ones of `Proof/Defs.lean`, repeated verbatim).
Nothing in this file is used by the proof.
-/
import Mathlib

namespace Erdos167Challenge

open Classical in
/-- The triangles of `G`: its 3-element cliques. -/
noncomputable def triangles {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Finset V) :=
  ((Finset.univ : Finset V).powersetCard 3).filter (fun T => G.IsClique (T : Set V))

/-- The edge set of a vertex set `T`: the non-diagonal pairs of `T`. -/
def edgesOf {V : Type*} [DecidableEq V] (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ¬ e.IsDiag)

/-- `F` is a family of pairwise edge-disjoint triangles of `G`. -/
def IsPacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Finset V)) : Prop :=
  F ⊆ triangles G ∧ (F : Set (Finset V)).PairwiseDisjoint edgesOf

open Classical in
/-- `ν(G)`: the largest number of pairwise edge-disjoint triangles of `G`. -/
noncomputable def packingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset V))).filter (fun F => IsPacking G F)).sup Finset.card

/-- Deleting the edges in `D` leaves `G` triangle-free. -/
def IsCover {V : Type*} (G : SimpleGraph V) (D : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges (D : Set (Sym2 V))).CliqueFree 3

/-- `τ(G)`: the least number of edges whose deletion leaves `G` triangle-free. -/
noncomputable def coverNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = m}

theorem not_exists_coverNumber_gt (n : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), 3 * packingNumber G < coverNumber G := by
  sorry

theorem coverNumber_le_three_mul_packingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : coverNumber G ≤ 3 * packingNumber G := by
  sorry

theorem exists_cover_of_packingNumber_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (hk : packingNumber G ≤ k) :
    ∃ D : Finset (Sym2 V), D.card ≤ 3 * k ∧ (G.deleteEdges (D : Set (Sym2 V))).CliqueFree 3 := by
  sorry

theorem coverNumber_le_card {V : Type*} (G : SimpleGraph V) (D : Finset (Sym2 V)) (h : IsCover G D) :
    coverNumber G ≤ D.card := by
  sorry

theorem exists_isCover_card_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = coverNumber G := by
  sorry

theorem card_le_packingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Finset V)) (h : IsPacking G F) : F.card ≤ packingNumber G := by
  sorry

end Erdos167Challenge
