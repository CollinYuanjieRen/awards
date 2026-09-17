import Erdos926Furedi.Embed

/-! In an `H_k`-free graph the rich graph at every vertex is `K_k`-free. -/

namespace Erdos926

open SimpleGraph Finset

/-- Auxiliary step: a `k`-clique of the rich graph at `x`, all of whose vertices are neighbours of
`x`, yields a copy of `H_k` in `G`.  The `k` clique vertices play the role of the `y_i`, and the
common neighbourhoods of the pairs, with `x` and the `y_i` removed, provide the sets `S p`. -/
private theorem isContained_of_isNClique (k : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {s : Finset V}
    (hs : (richGraph G (threshold k) x).IsNClique k s) (hx : ∀ v ∈ s, G.Adj x v) :
    Hk k ⊑ G := by
  classical
  -- enumerate the clique
  set e := s.equivFinOfCardEq hs.card_eq with he
  set y : Fin k → V := fun i => (e.symm i : V) with hy
  have hymem : ∀ i, y i ∈ s := fun i => (e.symm i).2
  have hyinj : Function.Injective y := by
    intro i j hij
    have h1 : e.symm i = e.symm j := Subtype.ext hij
    simpa using congrArg e h1
  have hrich : ∀ i j : Fin k, i ≠ j → threshold k ≤ codeg G (y i) (y j) := fun i j hij =>
    (hs.isClique (Finset.mem_coe.2 (hymem i)) (Finset.mem_coe.2 (hymem j))
      fun h => hij (hyinj h)).2.2.2
  refine isContained_of_rich k G x y hyinj (fun i => hx _ (hymem i))
    (fun p => (G.neighborFinset (y p.1.1) ∩ G.neighborFinset (y p.1.2)) \
      insert x (Finset.univ.image y)) ?_ ?_ ?_ ?_
  · intro p z hz
    have hz' := Finset.mem_inter.1 (Finset.mem_sdiff.1 hz).1
    exact ⟨(G.mem_neighborFinset _ _).1 hz'.1, (G.mem_neighborFinset _ _).1 hz'.2⟩
  · exact fun p h => (Finset.mem_sdiff.1 h).2 (Finset.mem_insert_self _ _)
  · exact fun p i h => (Finset.mem_sdiff.1 h).2
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem y (Finset.mem_univ i)))
  · intro p
    have h1 : threshold k ≤ (G.neighborFinset (y p.1.1) ∩ G.neighborFinset (y p.1.2)).card := by
      have := hrich p.1.1 p.1.2 (Fin.ne_of_lt p.2)
      simpa [codeg] using this
    have h2 : (insert x (Finset.univ.image y)).card ≤ k + 1 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := y)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      omega
    have h3 := Finset.le_card_sdiff (insert x (Finset.univ.image y))
      (G.neighborFinset (y p.1.1) ∩ G.neighborFinset (y p.1.2))
    simp only [threshold] at h1
    omega

/-- The counting statement, for every `k ≠ 1`: in an `H_k`-free graph the rich graph at `x` is
`K_k`-free.  (For `k = 1` the statement is false, see `richGraph_cliqueFree_one_false` below.) -/
theorem richGraph_cliqueFree_of_ne_one (k : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hk : k ≠ 1) (hfree : (Hk k).Free G) (x : V) :
    (richGraph G (threshold k) x).CliqueFree k := by
  intro s hs
  refine hfree (isContained_of_isNClique k G x hs ?_)
  -- every vertex of the clique is a neighbour of `x`: for `k ≥ 2` it has a clique partner, and
  -- for `k = 0` the clique is empty
  intro v hv
  rcases Nat.lt_or_ge k 2 with hklt | hk2
  · interval_cases k
    · exact absurd hs.card_eq (Finset.card_ne_zero_of_mem hv)
    · exact absurd rfl hk
  · have hcard : 1 < s.card := by rw [hs.card_eq]; omega
    have hne : (s.erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv]; omega
    obtain ⟨w, hw⟩ := hne
    exact (hs.isClique (Finset.mem_coe.2 (Finset.mem_of_mem_erase hw))
      (Finset.mem_coe.2 hv) (Finset.ne_of_mem_erase hw)).2.2.1

/-- **The frozen statement is false for `k = 1`.**  `H_1` is a single edge, so the empty graph on
one vertex is `H_1`-free, while `CliqueFree 1` fails for it (every singleton is a `1`-clique).
Hence `richGraph_cliqueFree` below cannot be proved as stated; it needs `k ≠ 1` (or `2 ≤ k`). -/
theorem richGraph_cliqueFree_one_false : (Hk 1).Free (⊥ : SimpleGraph (Fin 1)) ∧
    ¬ (richGraph (⊥ : SimpleGraph (Fin 1)) (threshold 1) 0).CliqueFree 1 := by
  constructor
  · refine SimpleGraph.free_bot ?_
    intro h
    have hadj : (Hk 1).Adj none (some (Sum.inl 0)) := trivial
    rw [h] at hadj
    exact hadj
  · intro h
    exact h {0} (SimpleGraph.isNClique_singleton.2 rfl)

theorem richGraph_cliqueFree (k : ℕ) (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : (Hk k).Free G) (x : V) :
    (richGraph G (threshold k) x).CliqueFree k :=
  richGraph_cliqueFree_of_ne_one k G (by omega) hfree x

end Erdos926
