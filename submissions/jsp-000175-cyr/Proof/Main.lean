import Proof.Defs

/-!
# Erdős problem #181 — the trivial bound `R(Q_n) ≤ R(K_{2^n}) ≤ 4^{2^n}`

The chain proved here is the one the problem page records as trivial:

* (T5) a monochromatic `K_m` inside a colouring `R` of `K_N` contains a copy of *every* graph
  `G` on `m` vertices, since `G` embeds injectively into the complete graph on its own vertices;
* (T4) hence `r(m, m)` vertices already force a monochromatic copy of any `G` on `m` vertices;
* (T3) so `R(G) ≤ R(m)` whenever `G` has `m` vertices;
* (T2) the hypercube `Q_n` has `2 ^ n` vertices, so `R(Q_n) ≤ R(K_{2^n})`;
* (T1) combining with the Erdős–Szekeres bound `R(k) ≤ 4 ^ k` gives `R(Q_n) ≤ 4 ^ (2 ^ n)`.

Not claimed here: the question `R(Q_n) ≪ 2^n` of the problem page (the Burr–Erdős conjecture), the
successive improvements of the trivial bound, and Tikhomirov's `R(Q_n) ≪ 2^{(2−c)n}`.
-/

namespace Erdos181

open SimpleGraph

/-- The hypercube `Q_n` has `2^n` vertices. -/
theorem card_hypercube (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- (T5) A red or blue `K_m` contains a copy of every graph on `m` vertices: if `R` is not
`m`-clique-free then `G ⊑ R` for every `G` on a vertex type of cardinality `m`. -/
theorem isContained_of_not_cliqueFree {V : Type*} [Fintype V] (G : SimpleGraph V) {N : ℕ} (R : SimpleGraph (Fin N)) (hR : ¬ R.CliqueFree (Fintype.card V)) : G ⊑ R := by
  classical
  -- A clique of size `Fintype.card V` in `R` is an embedded complete graph on `Fin (card V)`.
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hR
  -- Relabel the vertices of `G` by `Fin (card V)` and push them into that clique.
  let q := Fintype.equivFin V
  refine ⟨⟨⟨fun v => e (q v), ?_⟩, ?_⟩⟩
  · intro a b hab
    exact e.map_rel_iff.mpr (q.injective.ne (G.ne_of_adj hab))
  · intro a b hab
    exact q.injective (e.injective hab)

/-- (T4) `r(m, m)` vertices suffice for every graph `G` on `m` vertices. -/
theorem graphRamseyProp_ramsey {V : Type*} [Fintype V] (G : SimpleGraph V) : GraphRamseyProp (ramsey (Fintype.card V) (Fintype.card V)) G := by
  classical
  intro Rc
  have h := ramseyProp_ramsey (Fintype.card V) (Fintype.card V) Rc
  by_cases hR : Rc.CliqueFree (Fintype.card V)
  · -- The red colour has no `K_m`, so by the Ramsey property the blue colour must have one.
    right
    exact isContained_of_not_cliqueFree G Rcᶜ (fun hc => h ⟨hR, hc⟩)
  · exact Or.inl (isContained_of_not_cliqueFree G Rc hR)

/-- (T3) `R(G) ≤ R(m)` for every graph `G` on `m` vertices. -/
theorem graphRamsey_le_R {V : Type*} [Fintype V] (G : SimpleGraph V) : graphRamsey G ≤ R (Fintype.card V) :=
  Nat.sInf_le (graphRamseyProp_ramsey G)

/-- (T2) The page's `R(Q_n) ≤ R(K_{2^n})`. -/
theorem graphRamsey_hypercube_le_R (n : ℕ) : graphRamsey (hypercube n) ≤ R (2 ^ n) := by
  have h := graphRamsey_le_R (hypercube n)
  rwa [card_hypercube] at h

/-- (T1) Audited root: the page's trivial bound `R(Q_n) ≤ C^{2^n}` with `C = 4`. -/
theorem graphRamsey_hypercube_le (n : ℕ) : graphRamsey (hypercube n) ≤ 4 ^ (2 ^ n) :=
  (graphRamsey_hypercube_le_R n).trans (ramsey_diag_le_four_pow (2 ^ n))

end Erdos181
