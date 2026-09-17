import MerLeanExperiment.Defs

/-!
# Erdős #915 for `m = 2`: the trivial case, both readings

A finite graph with at least as many edges as vertices contains a cycle, and a cycle through `u`
splits at its first edge `u–v` into two internally disjoint `u`–`v` paths.  Internally disjoint
paths between distinct vertices are automatically edge-disjoint, which settles the edge reading.
-/

namespace Erdos915

open SimpleGraph

/-- A finite graph on at least one vertex with at least as many edges as vertices is not a
forest. -/
theorem not_isAcyclic_of_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ G.edgeSet.ncard) (hV : 1 ≤ Fintype.card V) : ¬ G.IsAcyclic := by
  intro hac
  have hne : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨F, hGF, -, hFac, hreach⟩ :=
    SimpleGraph.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic (G := ⊤) le_top hac
  have hpre : F.Preconnected := by
    intro a b
    rw [hreach]
    exact SimpleGraph.connected_top.preconnected a b
  have htree : F.IsTree := ⟨⟨hpre⟩, hFac⟩
  have hcard : Nat.card F.edgeSet + 1 = Nat.card V :=
    (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hcard
  have hsub : G.edgeSet.ncard ≤ F.edgeSet.ncard :=
    Set.ncard_le_ncard (edgeSet_mono hGF) (Set.toFinite _)
  omega

/-- A finite graph on at least one vertex with at least as many edges as vertices has two
vertices joined by two internally disjoint paths. -/
theorem hasVertexRails_two_of_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ G.edgeSet.ncard) (hV : 1 ≤ Fintype.card V) : HasVertexRails G 2 := by
  have hnac : ¬ G.IsAcyclic := not_isAcyclic_of_card_le G h hV
  have hcyc : ∃ (x : V) (c : G.Walk x x), c.IsCycle := by
    by_contra hcon
    push Not at hcon
    exact hnac fun x c hc ↦ hcon x c hc
  obtain ⟨u, c, hc⟩ := hcyc
  cases c with
  | nil => simp at hc
  | @cons _ w _ hadj p =>
    obtain ⟨hp, hedge⟩ := (Walk.cons_isCycle_iff p hadj).mp hc
    have hne : (Walk.cons hadj Walk.nil : G.Walk u w) ≠ p.reverse := by
      intro heq
      apply hedge
      have hmem : s(u, w) ∈ (Walk.cons hadj Walk.nil : G.Walk u w).edges := by simp
      rw [heq, Walk.edges_reverse, List.mem_reverse] at hmem
      exact hmem
    have hsupp : ∀ z : V,
        z ∈ (Walk.cons hadj Walk.nil : G.Walk u w).support →
          z = u ∨ z = w := by
      intro z hz
      simpa using hz
    refine ⟨u, w, hadj.ne, ![Walk.cons hadj Walk.nil, p.reverse],
      ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · simp [Walk.cons_isPath_iff, hadj.ne]
      · simpa using hp.reverse
    · intro i j hij z hzi hzj
      fin_cases i
      · exact hsupp z (by simpa using hzi)
      · fin_cases j
        · exact hsupp z (by simpa using hzj)
        · exact absurd rfl hij

/-- A path from `u` to `v` that uses the edge `uv` is the single-edge walk. -/
theorem eq_cons_nil_of_mem_edges {V : Type*} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (hadj : G.Adj u v) (he : s(u, v) ∈ p.edges) :
    p = Walk.cons hadj Walk.nil := by
  cases p with
  | nil => simp at he
  | @cons _ w _ h' q =>
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · have hw : w = v := (Sym2.congr_right.mp he).symm
      subst hw
      rw [Walk.eq_nil_iff_nil.mpr
        (Walk.isPath_iff_nil.mp ((Walk.cons_isPath_iff h' q).mp hp).1)]
    · exact absurd (Walk.fst_mem_support_of_mem_edges q he)
        ((Walk.cons_isPath_iff h' q).mp hp).2

/-- Internally disjoint paths between two distinct vertices are edge-disjoint. -/
theorem hasEdgeRails_of_hasVertexRails {V : Type*} (G : SimpleGraph V) (m : ℕ)
    (h : HasVertexRails G m) : HasEdgeRails G m := by
  obtain ⟨u, v, huv, p, hinj, hpath, hdisj⟩ := h
  refine ⟨u, v, huv, p, hpath, ?_⟩
  intro i j hij e
  induction e using Sym2.ind with
  | _ a b =>
    intro hei hej
    have hab : G.Adj a b := (p i).adj_of_mem_edges hei
    have ha : a = u ∨ a = v :=
      hdisj i j hij a (Walk.fst_mem_support_of_mem_edges _ hei)
        (Walk.fst_mem_support_of_mem_edges _ hej)
    have hb : b = u ∨ b = v :=
      hdisj i j hij b (Walk.snd_mem_support_of_mem_edges _ hei)
        (Walk.snd_mem_support_of_mem_edges _ hej)
    have hsym : s(a, b) = s(u, v) := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;>
        first
          | rfl
          | exact Sym2.eq_swap
          | exact absurd hab (by simp)
    rw [hsym] at hei hej
    have hadj : G.Adj u v := (p i).adj_of_mem_edges hei
    exact hij (hinj ((eq_cons_nil_of_mem_edges (hpath i) hadj hei).trans
      (eq_cons_nil_of_mem_edges (hpath j) hadj hej).symm))

/-- A finite graph on at least one vertex with at least as many edges as vertices has two
vertices joined by two edge-disjoint paths. -/
theorem hasEdgeRails_two_of_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ G.edgeSet.ncard) (hV : 1 ≤ Fintype.card V) : HasEdgeRails G 2 :=
  hasEdgeRails_of_hasVertexRails G 2 (hasVertexRails_two_of_card_le G h hV)

/-- The Bollobás–Erdős conjecture for `m = 2`, vertex-disjoint reading. -/
theorem vertex_rails_two {n : ℕ} (_hn : 1 ≤ n) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (2 - 1)) (hE : G.edgeSet.ncard = 1 + n * Nat.choose 2 2) :
    HasVertexRails G 2 := by
  rw [Nat.choose_self] at hE
  exact hasVertexRails_two_of_card_le G (by omega) (by omega)

/-- The Bollobás–Erdős conjecture for `m = 2`, edge-disjoint reading. -/
theorem edge_rails_two {n : ℕ} (_hn : 1 ≤ n) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (2 - 1)) (hE : G.edgeSet.ncard = 1 + n * Nat.choose 2 2) :
    HasEdgeRails G 2 := by
  rw [Nat.choose_self] at hE
  exact hasEdgeRails_two_of_card_le G (by omega) (by omega)

end Erdos915
