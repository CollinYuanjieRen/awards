import MerLeanExperiment.RamseyDefs

/-!
# Erdős problem #551 — finiteness of the Ramsey numbers

Reused from our own JSP-000669 package (Erdős #812), via our JSP-000099 and JSP-000175 packages.

This Mathlib pin has no two-colour graph Ramsey theorem, so we prove the finiteness
statement `∃ N, RamseyProp N m n` here, by the classical induction
`r(m, n) ≤ r(m-1, n) + r(m, n-1)` (in the slightly lossy form
`RamseyProp (A + B + 1) m n`).

The workhorse is `Erdos551.exists_clique_of_subset`: a set of at least `A` vertices, where
`A` has the Ramsey property for `(m, n)`, contains a red `K_m` or a blue `K_n`.
-/

namespace Erdos551

open SimpleGraph

/-- If `RamseyProp A m n` holds and `s` is a set of at least `A` vertices of a colouring `G`,
then `s` contains a red `K_m` or a blue `K_n`. -/
theorem exists_clique_of_subset {N A m n : ℕ} (G : SimpleGraph (Fin N)) (s : Finset (Fin N))
    (hA : A ≤ s.card) (hR : RamseyProp A m n) :
    (∃ t ⊆ s, G.IsNClique m t) ∨ (∃ t ⊆ s, Gᶜ.IsNClique n t) := by
  classical
  let g : Fin A → Fin N := fun i => ((s.equivFin.symm (Fin.castLE hA i) : {x // x ∈ s}) : Fin N)
  have hgs : ∀ i, g i ∈ s := fun i => (s.equivFin.symm (Fin.castLE hA i)).2
  have hginj : Function.Injective g := by
    intro i j hij
    have h1 : s.equivFin.symm (Fin.castLE hA i) = s.equivFin.symm (Fin.castLE hA j) :=
      Subtype.ext hij
    exact (Fin.castLEEmb hA).injective (s.equivFin.symm.injective h1)
  let e : Fin A ↪ Fin N := ⟨g, hginj⟩
  have hmem : ∀ {t : Finset (Fin A)}, t.map e ⊆ s := by
    intro t x hx
    simp only [Finset.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hgs i
  have hbad := hR (G.comap e)
  simp only [IsGood, not_and_or] at hbad
  rcases hbad with hbad | hbad
  · left
    simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hbad
    obtain ⟨t, ht⟩ := hbad
    exact ⟨t.map e, hmem, isNClique_map_comap e G ht⟩
  · right
    rw [compl_comap] at hbad
    simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hbad
    obtain ⟨t, ht⟩ := hbad
    exact ⟨t.map e, hmem, isNClique_map_comap e Gᶜ ht⟩

/-- The classical induction step: if `A` works for `(m-1, n)` and `B` works for `(m, n-1)`,
then `A + B + 1` works for `(m, n)`. -/
theorem ramseyProp_step {A B m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hA : RamseyProp A (m - 1) n) (hB : RamseyProp B m (n - 1)) :
    RamseyProp (A + B + 1) m n := by
  classical
  intro G hG
  let v : Fin (A + B + 1) := ⟨0, Nat.succ_pos _⟩
  have hdisj : Disjoint (G.neighborFinset v) (Gᶜ.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj] at hw'
    exact hw'.2 hw
  have hunion : G.neighborFinset v ∪ Gᶜ.neighborFinset v = Finset.univ.erase v := by
    ext w
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact (G.ne_of_adj h).symm
      · exact fun hc => h hc.symm
    · intro h
      by_cases hadj : G.Adj v w
      · exact Or.inl hadj
      · exact Or.inr ⟨fun hc => h hc.symm, hadj⟩
  have hcard : (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card = A + B := by
    have h1 := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v)] at h1
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hsplit : A ≤ (G.neighborFinset v).card ∨ B ≤ (Gᶜ.neighborFinset v).card := by omega
  rcases hsplit with h | h
  · rcases exists_clique_of_subset G _ h hA with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · have hv : ∀ b ∈ t, G.Adj v b := by
        intro b hb
        have hb' := hts hb
        rw [SimpleGraph.mem_neighborFinset] at hb'
        exact hb'
      have hcl := ht.insert hv
      rw [show m - 1 + 1 = m by omega] at hcl
      exact hG.1 _ hcl
    · exact hG.2 _ ht
  · rcases exists_clique_of_subset G _ h hB with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · exact hG.1 _ ht
    · have hv : ∀ b ∈ t, Gᶜ.Adj v b := by
        intro b hb
        have hb' := hts hb
        rw [SimpleGraph.mem_neighborFinset] at hb'
        exact hb'
      have hcl := ht.insert hv
      rw [show n - 1 + 1 = n by omega] at hcl
      exact hG.2 _ hcl

/-- Zero vertices already force a red `K_0`. -/
theorem ramseyProp_zero_left (n : ℕ) : RamseyProp 0 0 n :=
  fun _ hG => SimpleGraph.not_cliqueFree_zero hG.1

/-- Zero vertices already force a blue `K_0`. -/
theorem ramseyProp_zero_right (m : ℕ) : RamseyProp 0 m 0 :=
  fun _ hG => SimpleGraph.not_cliqueFree_zero hG.2

/-- One vertex already forces a red `K_1`. -/
theorem ramseyProp_one_left (n : ℕ) : RamseyProp 1 1 n := by
  intro G hG
  exact (SimpleGraph.cliqueFree_one.mp hG.1).false (0 : Fin 1)

/-- One vertex already forces a blue `K_1`. -/
theorem ramseyProp_one_right (m : ℕ) : RamseyProp 1 m 1 := by
  intro G hG
  exact (SimpleGraph.cliqueFree_one.mp hG.2).false (0 : Fin 1)

/-- **Ramsey's theorem for two colours**: for all `m, n` there is an `N` such that every
red/blue colouring of `K_N` contains a red `K_m` or a blue `K_n`. -/
theorem exists_ramseyProp (m n : ℕ) : ∃ N, RamseyProp N m n := by
  have key : ∀ k m n : ℕ, m + n ≤ k → ∃ N, RamseyProp N m n := by
    intro k
    induction k with
    | zero =>
      intro m n h
      have hm : m = 0 := by omega
      subst hm
      exact ⟨0, ramseyProp_zero_left n⟩
    | succ k ih =>
      intro m n h
      by_cases hm0 : m = 0
      · subst hm0; exact ⟨0, ramseyProp_zero_left n⟩
      by_cases hn0 : n = 0
      · subst hn0; exact ⟨0, ramseyProp_zero_right m⟩
      by_cases hm1 : m = 1
      · subst hm1; exact ⟨1, ramseyProp_one_left n⟩
      by_cases hn1 : n = 1
      · subst hn1; exact ⟨1, ramseyProp_one_right m⟩
      obtain ⟨A, hA⟩ := ih (m - 1) n (by omega)
      obtain ⟨B, hB⟩ := ih m (n - 1) (by omega)
      exact ⟨A + B + 1, ramseyProp_step (by omega) (by omega) hA hB⟩
  exact key (m + n) m n le_rfl

/-- The Ramsey number `r(m, n)` itself has the Ramsey property. -/
theorem ramseyProp_ramsey (m n : ℕ) : RamseyProp (ramsey m n) m n :=
  Nat.sInf_mem (exists_ramseyProp m n)

/-- A good colouring of `K_N` witnesses `N < r(m, n)`. -/
theorem lt_ramsey_of_isGood {N m n : ℕ} {G : SimpleGraph (Fin N)} (hG : IsGood G m n) :
    N < ramsey m n := by
  by_contra hc
  simp only [not_lt] at hc
  exact ramseyProp_mono hc (ramseyProp_ramsey m n) G hG

end Erdos551
