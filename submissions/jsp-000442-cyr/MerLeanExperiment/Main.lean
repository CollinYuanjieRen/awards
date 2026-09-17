import MerLeanExperiment.Defs

/-!
# Erdős problem #551 — the lower bound `(k − 1)(n − 1) + 1 ≤ R(C_k, K_n)`
-/

namespace Erdos551

open SimpleGraph

/-- (T6) A red or blue `K_m` contains a copy of every graph on `m` vertices (reused from our
JSP-000175 package). -/
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

/-- (T5) `r(|α|, |β|)` vertices suffice: `R(G, H)` is finite, so the `sInf` defining it is honest. -/
theorem graphRamseyProp_ramsey {α β : Type*} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β) : GraphRamseyProp (ramsey (Fintype.card α) (Fintype.card β)) G H := by
  classical
  intro Rc
  have h := ramseyProp_ramsey (Fintype.card α) (Fintype.card β) Rc
  by_cases hR : Rc.CliqueFree (Fintype.card α)
  · -- The red colour has no `K_m`, so by the Ramsey property the blue colour must have one.
    right
    exact isContained_of_not_cliqueFree H Rcᶜ (fun hc => h ⟨hR, hc⟩)
  · exact Or.inl (isContained_of_not_cliqueFree G Rc hR)

/-- (T4) The Ramsey property is monotone in the number of vertices. -/
theorem graphRamseyProp_mono {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {N N' : ℕ} (h : N ≤ N') (hN : GraphRamseyProp N G H) : GraphRamseyProp N' G H := by
  intro R'
  rcases hN (R'.comap (Fin.castLEEmb h)) with hG | hH
  · exact Or.inl (hG.trans ⟨(SimpleGraph.Embedding.comap (Fin.castLEEmb h) R').toCopy⟩)
  · rw [compl_comap] at hH
    exact Or.inr (hH.trans ⟨(SimpleGraph.Embedding.comap (Fin.castLEEmb h) R'ᶜ).toCopy⟩)

/-- A quantity that is constant along the edges of the target graph is constant along the image of
a walk in the source graph. -/
theorem eq_of_walk_of_hom {V W γ : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (blk : W → γ) (hblk : ∀ x y, H.Adj x y → blk x = blk y)
    {u v : V} (p : G.Walk u v) : blk (f u) = blk (f v) := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hblk _ _ (f.map_adj hadj)).trans ih

/-- (T3) The blow-up colouring with `n` red cliques of size `k` has no red `C_{k+1}` and no blue
`K_{n+1}`. -/
theorem not_graphRamseyProp_blowUp (k n : ℕ) : ¬ GraphRamseyProp (n * k) (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1))) := by
  classical
  intro hP
  set e : Fin n × Fin k ≃ Fin (n * k) := finProdFinEquiv with he
  set R : SimpleGraph (Fin (n * k)) := (blowUp n k).comap e.symm.toEmbedding with hR
  have hadj : ∀ x y : Fin (n * k), R.Adj x y ↔ (x ≠ y ∧ (e.symm x).1 = (e.symm y).1) := by
    intro x y
    simp only [hR, SimpleGraph.comap_adj, blowUp, SimpleGraph.fromRel_adj,
      Equiv.coe_toEmbedding, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro ⟨hne, h | h⟩
      · exact ⟨hne, h⟩
      · exact ⟨hne, h.symm⟩
    · rintro ⟨hne, h⟩
      exact ⟨hne, Or.inl h⟩
  have hblk : ∀ x y : Fin (n * k), R.Adj x y → (e.symm x).1 = (e.symm y).1 :=
    fun x y h => ((hadj x y).1 h).2
  rcases hP R with hcyc | htop
  · -- A red `C_{k+1}` would lie inside a single block, which has only `k` vertices.
    obtain ⟨f⟩ : Nonempty (Copy (cycleGraph (k + 1)) R) := hcyc
    have hconst : ∀ v : Fin (k + 1), (e.symm (f.toHom v)).1 = (e.symm (f.toHom 0)).1 := by
      intro v
      exact (cycleGraph_connected (n := k)).preconnected v 0 |>.elim fun p =>
        eq_of_walk_of_hom f.toHom (fun x => (e.symm x).1) hblk p
    have hinj : Function.Injective (fun v : Fin (k + 1) => (e.symm (f.toHom v)).2) := by
      intro a b hab
      apply f.injective
      apply e.symm.injective
      refine Prod.ext ?_ ?_
      · rw [hconst a, hconst b]
      · exact hab
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin, Fintype.card_fin] at hcard
    omega
  · -- A blue `K_{n+1}` would need `n + 1` distinct blocks.
    obtain ⟨g⟩ : Nonempty (Copy (⊤ : SimpleGraph (Fin (n + 1))) Rᶜ) := htop
    obtain ⟨a, b, hab, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun v : Fin (n + 1) => (e.symm (g.toHom v)).1) (by simp)
    have hne : g.toHom a ≠ g.toHom b := fun h => hab (g.injective h)
    have hcompl : Rᶜ.Adj (g.toHom a) (g.toHom b) :=
      g.toHom.map_adj (by simpa using hab)
    rw [SimpleGraph.compl_adj] at hcompl
    exact hcompl.2 ((hadj _ _).2 ⟨hne, heq⟩)

/-- (T1) Audited root: `k · n + 1 ≤ R(C_{k+1}, K_{n+1})` for all `k, n`, i.e.
`(k − 1)(n − 1) + 1 ≤ R(C_k, K_n)` for all `k, n ≥ 1`. -/
theorem lower_bound (k n : ℕ) : k * n + 1 ≤ graphRamsey (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1))) := by
  by_contra hcon
  have hne : {N : ℕ | GraphRamseyProp N (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1)))}.Nonempty :=
    ⟨_, graphRamseyProp_ramsey (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1)))⟩
  have hmem : GraphRamseyProp (graphRamsey (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1))))
      (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1))) := Nat.sInf_mem hne
  have h1 : graphRamsey (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1))) ≤ k * n :=
    Nat.le_of_lt_succ (Nat.not_le.mp hcon)
  have hle : graphRamsey (cycleGraph (k + 1)) (⊤ : SimpleGraph (Fin (n + 1))) ≤ n * k := by
    rw [Nat.mul_comm]; exact h1
  exact not_graphRamseyProp_blowUp k n (graphRamseyProp_mono hle hmem)

/-- (T2) The page's form of the lower half of the identity, for `k ≥ 3` and `n ≥ 3`. -/
theorem lower_bound' (k n : ℕ) (hk : 3 ≤ k) (hn : 3 ≤ n) : (k - 1) * (n - 1) + 1 ≤ graphRamsey (cycleGraph k) (⊤ : SimpleGraph (Fin n)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simpa using lower_bound k' n'

end Erdos551
