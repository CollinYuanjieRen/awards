import Proof.Defs

/-!
# Clique transversals of triangle-free graphs: the bound `τ(G) ≤ n − H(n)`

This module proves the scoped component of Erdős problem #151 recorded in `Defs.lean`:
every triangle-free graph `G` on `n` vertices satisfies `τ(G) ≤ n − H(n)`.

The argument is short.  If `S` is an independent set of `G`, then every clique of `G` meets
`S` in at most one vertex, so the complement `univ \ S` meets every clique on at least two
vertices; in particular `univ \ S` is a clique transversal and `τ(G) ≤ |V| − |S|`.  Taking `S`
of maximum size gives `τ(G) ≤ |V| − α(G)` (`cliqueTransversalNum_le_card_sub_indepNum`).  For a
triangle-free graph on `Fin n` the independence number is at least `H n`
(`H_le_indepNum`, which needs that the `sSup` defining `H` is attained), and the two bounds
combine into the statement.

Not claimed here: the general question `τ(G) ≤ n − H(n)` for arbitrary graphs `G`, the bound
`τ(G) ≤ n − √n` and the `K₄`-free case discussed on the problem page.
-/

namespace Erdos151

open SimpleGraph

/-- (T5) The complement of an independent set meets every maximal clique on at least two
vertices. -/
theorem isCliqueTransversal_compl_of_isIndepSet {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (hS : G.IsIndepSet (S : Set V)) : IsCliqueTransversal G (Finset.univ \ S) := by
  intro s hs h2
  by_contra hne
  -- No vertex of `s` lies outside `S`, i.e. `s ⊆ S`.
  have hsub : ∀ v ∈ s, v ∈ S := by
    intro v hv
    by_contra hvS
    exact hne ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvS⟩, hv⟩
  -- `s` has two distinct vertices, which are adjacent (clique) and nonadjacent (independent).
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  have hadj : G.Adj a b := hs.1 (by exact_mod_cast ha) (by exact_mod_cast hb) hab
  exact ((SimpleGraph.isIndepSet_iff G).mp hS) (by exact_mod_cast hsub a ha)
    (by exact_mod_cast hsub b hb) hab hadj

/-- The whole vertex set is a clique transversal. -/
theorem isCliqueTransversal_univ {V : Type*} [Fintype V] (G : SimpleGraph V) : IsCliqueTransversal G Finset.univ := by
  intro s _ h2
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two h2)
  exact ⟨v, Finset.mem_univ v, hv⟩

/-- (T3) `τ(G) ≤ |V| − α(G)` for every finite graph. -/
theorem cliqueTransversalNum_le_card_sub_indepNum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : cliqueTransversalNum G ≤ Fintype.card V - G.indepNum := by
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  refine Nat.sInf_le ⟨Finset.univ \ S, ?_, isCliqueTransversal_compl_of_isIndepSet G S hS.isIndepSet⟩
  rw [Finset.card_univ_sdiff, hS.card_eq]

/-- (T4) `H(n)` is attained: every triangle-free graph on `n` vertices has independence number at
least `H(n)`. -/
theorem H_le_indepNum (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) : H n ≤ G.indepNum := by
  have hne : {h : ℕ | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → h ≤ G.indepNum}.Nonempty :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have hbdd : BddAbove {h : ℕ | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → h ≤ G.indepNum} :=
    ⟨(⊥ : SimpleGraph (Fin n)).indepNum,
      fun _ hh => hh ⊥ (SimpleGraph.cliqueFree_bot (by norm_num))⟩
  exact Nat.sSup_mem hne hbdd G hG

/-- (T2) Triangle-free graphs satisfy `τ(G) ≤ n − H(n)`. -/
theorem cliqueTransversalNum_le_of_cliqueFree (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) : cliqueTransversalNum G ≤ n - H n := by
  calc cliqueTransversalNum G ≤ Fintype.card (Fin n) - G.indepNum :=
        cliqueTransversalNum_le_card_sub_indepNum G
    _ = n - G.indepNum := by rw [Fintype.card_fin]
    _ ≤ n - H n := Nat.sub_le_sub_left (H_le_indepNum n G hG) n

/-- (T1) Audited root: no triangle-free graph on `n` vertices has `τ(G) > n − H(n)`. -/
theorem not_exists_triangleFree_gt (n : ℕ) : ¬ ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ n - H n < cliqueTransversalNum G := by
  rintro ⟨G, hG, hlt⟩
  exact absurd (cliqueTransversalNum_le_of_cliqueFree n G hG) (not_le.mpr hlt)

end Erdos151
