import Proof.Defs

/-!
# Erdős problem #87 — the case `ε ≥ 3/4` is trivial because `R(k) ≤ 4^k`

The problem page asks whether `R(G) > (1 − ε)^k R(k)` for every graph `G` with chromatic number
`k`, and records that "since `R(k) ≤ 4^k` this is trivial for `ε ≥ 3/4`".  This file proves that
remark:

* (T5) a graph with chromatic number at least `2` is not empty, so it has an edge;
* (T4) a graph with an edge needs at least `2` vertices to host a monochromatic copy, so
  `R(G) ≥ 2`;
* (T3) combined with the Erdős–Szekeres bound `R(k) ≤ 4^k` this gives `R(k) < 4^k · R(G)`
  whenever `χ(G) = k ≥ 2`;
* (T2) dividing by `4^k` and using `(1 − ε)^k ≤ (1/4)^k` for `3/4 ≤ ε ≤ 1` gives the page's
  inequality `R(G) > (1 − ε)^k R(k)`;
* (T1) the audited root: no counterexample to `R(k) < 4^k · R(G)` exists.

Not claimed here: the two open questions of the problem page (the inequality for every `ε > 0`,
and a constant `c > 0` with `R(G) > c R(k)`), Erdős's original conjecture `R(G) ≥ R(k)`, the
Faudree–McKay computation `R(W) = 17` for the pentagonal wheel, and Wigderson's `R(G) ≫ 2^{k/2}`.

The nonemptiness of the set defining `R(G)` comes from `Erdos87.graphRamseyProp_ramsey`, reused
from our own JSP-000175 package (Erdős #181) together with its ingredient
`Erdos87.isContained_of_not_cliqueFree`.
-/

namespace Erdos87

open SimpleGraph

/-- A red or blue `K_m` contains a copy of every graph on `m` vertices: if `R` is not
`m`-clique-free then `G ⊑ R` for every `G` on a vertex type of cardinality `m`.
Reused from our own JSP-000175 package (Erdős #181). -/
theorem isContained_of_not_cliqueFree {V : Type*} [Fintype V] (G : SimpleGraph V) {N : ℕ}
    (R : SimpleGraph (Fin N)) (hR : ¬ R.CliqueFree (Fintype.card V)) : G ⊑ R := by
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

/-- `r(m, m)` vertices suffice for every graph `G` on `m` vertices; in particular the set whose
infimum defines `R(G)` is nonempty.  Reused from our own JSP-000175 package (Erdős #181). -/
theorem graphRamseyProp_ramsey {V : Type*} [Fintype V] (G : SimpleGraph V) :
    GraphRamseyProp (ramsey (Fintype.card V) (Fintype.card V)) G := by
  classical
  intro Rc
  have h := ramseyProp_ramsey (Fintype.card V) (Fintype.card V) Rc
  by_cases hR : Rc.CliqueFree (Fintype.card V)
  · -- The red colour has no `K_m`, so by the Ramsey property the blue colour must have one.
    right
    exact isContained_of_not_cliqueFree G Rcᶜ (fun hc => h ⟨hR, hc⟩)
  · exact Or.inl (isContained_of_not_cliqueFree G Rc hR)

/-- (T5) A graph with chromatic number at least `2` has an edge. -/
theorem exists_adj_of_two_le_chromaticNumber {V : Type*} (G : SimpleGraph V) (h : 2 ≤ G.chromaticNumber) : ∃ u v : V, G.Adj u v := by
  by_contra hc
  -- Without an edge the graph is `⊥`, whose chromatic number is at most `1`.
  have hbot : G = ⊥ :=
    SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun a b => not_exists.mp (not_exists.mp hc a) b
  exact SimpleGraph.two_le_chromaticNumber_iff_ne_bot.mp h hbot

/-- (T4) A graph with an edge has graph Ramsey number at least `2`: on at most one vertex there is
no room for a monochromatic edge. -/
theorem two_le_graphRamsey_of_adj {V : Type*} [Fintype V] (G : SimpleGraph V) {u v : V} (h : G.Adj u v) : 2 ≤ graphRamsey G := by
  refine le_csInf ⟨_, graphRamseyProp_ramsey G⟩ fun N hN => ?_
  by_contra hlt
  -- Colour `K_N` all blue and look at the resulting monochromatic copy of `G`.
  rcases hN (⊥ : SimpleGraph (Fin N)) with hred | hblue
  · -- A red copy would need a red edge, but there are none.
    obtain ⟨f⟩ : Nonempty (G.Copy (⊥ : SimpleGraph (Fin N))) := hred
    exact (SimpleGraph.bot_adj _ _).mp (f.toHom.map_adj h)
  · -- A blue copy sends the edge `u ~ v` to two distinct vertices, so `N ≥ 2`.
    obtain ⟨f⟩ : Nonempty (G.Copy (⊥ : SimpleGraph (Fin N))ᶜ) := hblue
    have hne : f u ≠ f v := f.injective.ne (G.ne_of_adj h)
    have hcard : 1 < Fintype.card (Fin N) := Fintype.one_lt_card_iff.mpr ⟨f u, f v, hne⟩
    rw [Fintype.card_fin] at hcard
    omega

/-- (T3) The natural-number form: `R(k) < 4^k · R(G)` for every `G` with `χ(G) = k ≥ 2`. -/
theorem R_lt_four_pow_mul_graphRamsey {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) (hG : G.chromaticNumber = (k : ℕ∞)) : R k < 4 ^ k * graphRamsey G := by
  obtain ⟨u, v, huv⟩ :=
    exists_adj_of_two_le_chromaticNumber G (by rw [hG]; exact_mod_cast hk)
  have h2 : 2 ≤ graphRamsey G := two_le_graphRamsey_of_adj G huv
  have h4 : R k ≤ 4 ^ k := ramsey_diag_le_four_pow k
  have hpos : 0 < 4 ^ k := pow_pos (by norm_num : (0:ℕ) < 4) k
  calc R k ≤ 4 ^ k := h4
    _ < 4 ^ k * 2 := by omega
    _ ≤ 4 ^ k * graphRamsey G := Nat.mul_le_mul_left _ h2

/-- (T2) The page's inequality `R(G) > (1 − ε)^k R(k)` for `3/4 ≤ ε ≤ 1` and `χ(G) = k ≥ 2`. -/
theorem lt_graphRamsey_of_chromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) (hG : G.chromaticNumber = (k : ℕ∞)) (ε : ℝ) (hε : 3 / 4 ≤ ε) (hε1 : ε ≤ 1) : (1 - ε) ^ k * (R k : ℝ) < graphRamsey G := by
  have h3 : (R k : ℝ) < 4 ^ k * (graphRamsey G : ℝ) := by
    exact_mod_cast R_lt_four_pow_mul_graphRamsey G k hk hG
  -- `0 ≤ 1 - ε ≤ 1/4`, so `(1 - ε)^k ≤ (1/4)^k`.
  have hb : (0 : ℝ) ≤ 1 - ε := by linarith
  have hb' : 1 - ε ≤ 1 / 4 := by linarith
  have hpow : (1 - ε) ^ k ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ hb hb' k
  have hqpos : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
  -- Scaling `R(k) < 4^k · R(G)` by `(1/4)^k` gives `(1/4)^k · R(k) < R(G)`.
  have hcancel : (1 / 4 : ℝ) ^ k * ((4 : ℝ) ^ k * (graphRamsey G : ℝ)) = (graphRamsey G : ℝ) := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hkey : (1 / 4 : ℝ) ^ k * (R k : ℝ) < (graphRamsey G : ℝ) := by
    have := mul_lt_mul_of_pos_left h3 hqpos
    rwa [hcancel] at this
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hpow (by positivity)) hkey

/-- (T1) Audited root: no graph on `n` vertices with chromatic number `k ≥ 2` violates
`R(k) < 4^k · R(G)`. -/
theorem not_exists_four_pow_mul_graphRamsey_le (n k : ℕ) : ¬ ∃ G : SimpleGraph (Fin n), 2 ≤ k ∧ G.chromaticNumber = (k : ℕ∞) ∧ 4 ^ k * graphRamsey G ≤ R k := by
  rintro ⟨G, hk, hG, hle⟩
  exact absurd (R_lt_four_pow_mul_graphRamsey G k hk hG) (not_lt.mpr hle)

end Erdos87
