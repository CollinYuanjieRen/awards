import MerLeanExperiment.Defs

/-!
# Erdős #915 for `m = 3` (Bártfai 1960)

Transcription of the digest's route: a graph with `2|E| > 3(|V|-1)` contains a *theta*, i.e. two
vertices joined by three internally disjoint paths.
-/

namespace Erdos915

open SimpleGraph

/-- Splitting a cycle at two of its vertices gives two internally disjoint arcs which together
cover the edges and the vertices of the cycle. -/
theorem exists_arcs_of_isCycle {V : Type*} {G : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) {A B : V} (hA : A ∈ c.support) (hB : B ∈ c.support) (hAB : A ≠ B) :
    ∃ p q : G.Walk A B, p.IsPath ∧ q.IsPath ∧ p ≠ q ∧ InternallyDisjoint p q ∧
      (∀ e ∈ p.edges, e ∈ c.edges) ∧ (∀ e ∈ q.edges, e ∈ c.edges) ∧
      (∀ z ∈ p.support, z ∈ c.support) ∧ (∀ z ∈ q.support, z ∈ c.support) ∧
      (∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges) := by
  classical
  have hc' : (c.rotate A hA).IsCycle := hc.rotate hA
  have hB' : B ∈ (c.rotate A hA).support := by simpa using hB
  have hEperm : ∀ e : Sym2 V, e ∈ (c.rotate A hA).edges ↔ e ∈ c.edges :=
    fun e ↦ (c.rotate_edges A hA).perm.mem_iff
  have hVperm : ∀ z : V, z ∈ (c.rotate A hA).support ↔ z ∈ c.support := by
    intro z; simp
  set d : G.Walk A A := c.rotate A hA with hd
  set P : G.Walk A B := d.takeUntil B hB' with hP
  set Q : G.Walk B A := d.dropUntil B hB' with hQ
  have hspec : P.append Q = d := Walk.take_spec d hB'
  have hsupp : d.support = P.support ++ Q.support.tail := by
    rw [← hspec, Walk.support_append]
  have hedges : d.edges = P.edges ++ Q.edges := by rw [← hspec, Walk.edges_append]
  have hPnil : ¬ P.Nil := by rw [hP, Walk.nil_takeUntil]; exact hAB
  have hPp : P.IsPath := hc'.isPath_takeUntil hB'
  have hQp : Q.IsPath := by
    rw [← hspec] at hc'
    exact hc'.isPath_of_append_right hPnil
  have hnodup : (P.support.tail ++ Q.support.tail).Nodup := by
    have h := hc'.support_nodup
    rw [← hspec] at h
    rw [hspec, hsupp, ← Walk.cons_tail_support P, List.cons_append, List.tail_cons] at h
    exact h
  have hdisj : P.support.tail.Disjoint Q.support.tail := List.disjoint_of_nodup_append hnodup
  have hnodupE : d.edges.Nodup := hc'.isTrail.edges_nodup
  refine ⟨P, Q.reverse, hPp, hQp.reverse, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hPQ
    have hlen : 0 < P.length := Walk.not_nil_iff_lt_length.mp hPnil
    obtain ⟨e, he⟩ : ∃ e, e ∈ P.edges := by
      refine List.exists_mem_of_ne_nil _ fun h ↦ ?_
      rw [← Walk.length_edges, h] at hlen
      simp at hlen
    have heQ : e ∈ Q.edges := by
      have : e ∈ Q.reverse.edges := hPQ ▸ he
      rwa [Walk.edges_reverse, List.mem_reverse] at this
    rw [hedges] at hnodupE
    exact List.disjoint_of_nodup_append hnodupE he heQ
  · intro w hw hwq
    by_contra hcon
    push Not at hcon
    have h1 : w ∈ P.support.tail :=
      List.mem_of_ne_of_mem hcon.1 (by rwa [Walk.cons_tail_support])
    have h2 : w ∈ Q.support.tail := by
      have hw' : w ∈ Q.support := by rwa [Walk.support_reverse, List.mem_reverse] at hwq
      exact List.mem_of_ne_of_mem hcon.2 (by rwa [Walk.cons_tail_support])
    exact hdisj h1 h2
  · intro e he
    rw [← hEperm]
    rw [hedges]
    exact List.mem_append_left _ he
  · intro e he
    rw [Walk.edges_reverse, List.mem_reverse] at he
    rw [← hEperm, hedges]
    exact List.mem_append_right _ he
  · intro z hz
    rw [← hVperm]
    exact d.support_takeUntil_subset_support hB' hz
  · intro z hz
    rw [Walk.support_reverse, List.mem_reverse] at hz
    rw [← hVperm]
    exact d.support_dropUntil_subset_support hB' hz
  · intro e he
    rw [← hEperm, hedges, List.mem_append] at he
    rcases he with he | he
    · exact Or.inl he
    · exact Or.inr (by rwa [Walk.edges_reverse, List.mem_reverse])

/-- Along a path whose two endpoints lie in a set `S`, any edge lies on a subpath whose endpoints
lie in `S` and whose interior avoids `S`.  (Digest §T2 Step 4: the "first vertex of `V(a)`".) -/
theorem exists_subpath_avoiding {V : Type*} {G : SimpleGraph V} (S : Set V) (f : Sym2 V) :
    ∀ (n : ℕ) {x y : V} (P : G.Walk x y), P.length ≤ n → P.IsPath → x ∈ S → y ∈ S →
      f ∈ P.edges → ∃ (A B : V) (R : G.Walk A B), R.IsPath ∧ A ∈ S ∧ B ∈ S ∧ f ∈ R.edges ∧
        ∀ z ∈ R.support, z ∈ S → z = A ∨ z = B := by
  classical
  intro n
  induction n with
  | zero =>
    intro x y P hlen _ _ _ hf
    have : P.edges = [] := by
      rw [← List.length_eq_zero_iff, Walk.length_edges]
      omega
    rw [this] at hf
    simp at hf
  | succ n ih =>
    intro x y P hlen hPp hx hy hf
    by_cases hall : ∀ z ∈ P.support, z ∈ S → z = x ∨ z = y
    · exact ⟨x, y, P, hPp, hx, hy, hf, hall⟩
    · push Not at hall
      obtain ⟨z, hz, hzS, hzx, hzy⟩ := hall
      have hsplit : (P.takeUntil z hz).edges ++ (P.dropUntil z hz).edges = P.edges := by
        rw [← Walk.edges_append, Walk.take_spec]
      have h1 : (P.takeUntil z hz).length ≤ n := by
        have := Walk.length_takeUntil_lt_length hz hzy
        omega
      have h2 : (P.dropUntil z hz).length ≤ n := by
        have := Walk.length_dropUntil_lt_length hz hzx
        omega
      rw [← hsplit, List.mem_append] at hf
      rcases hf with hf | hf
      · exact ih _ h1 (hPp.takeUntil hz) hx hzS hf
      · exact ih _ h2 (hPp.dropUntil hz) hzS hy hf

/-- A cycle `c` together with a path `R` between two of its vertices whose interior avoids `c` and
which uses an edge off `c` is a theta subgraph, hence gives three internally disjoint paths. -/
theorem hasVertexRails_three_of_theta {V : Type*} {G : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) {A B : V} (hA : A ∈ c.support) (hB : B ∈ c.support) (hAB : A ≠ B)
    {R : G.Walk A B} (hR : R.IsPath) (hRc : ∀ z ∈ R.support, z ∈ c.support → z = A ∨ z = B)
    {g : Sym2 V} (hg : g ∈ R.edges) (hgc : g ∉ c.edges) : HasVertexRails G 3 := by
  obtain ⟨p, q, hp, hq, hpq, hpqd, hpe, hqe, hps, hqs, -⟩ := exists_arcs_of_isCycle hc hA hB hAB
  have hpR : p ≠ R := fun h ↦ hgc (hpe g (by rw [h]; exact hg))
  have hqR : q ≠ R := fun h ↦ hgc (hqe g (by rw [h]; exact hg))
  have hqpd : InternallyDisjoint q p := fun w h1 h2 ↦ hpqd w h2 h1
  have hpRd : InternallyDisjoint p R := fun w h1 h2 ↦ hRc w h2 (hps w h1)
  have hRpd : InternallyDisjoint R p := fun w h1 h2 ↦ hRc w h1 (hps w h2)
  have hqRd : InternallyDisjoint q R := fun w h1 h2 ↦ hRc w h2 (hqs w h1)
  have hRqd : InternallyDisjoint R q := fun w h1 h2 ↦ hRc w h1 (hqs w h2)
  refine ⟨A, B, hAB, ![p, q, R], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> simpa
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Two cycles sharing an edge, one of which has an edge off the other, give a theta.
(Digest §T2 Step 4.) -/
theorem hasVertexRails_three_of_cycles {V : Type*} {G : SimpleGraph V} {v w : V}
    {a : G.Walk v v} {b : G.Walk w w} (ha : a.IsCycle) (hb : b.IsCycle) {e : Sym2 V}
    (hea : e ∈ a.edges) (heb : e ∈ b.edges) {g : Sym2 V} (hgb : g ∈ b.edges)
    (hga : g ∉ a.edges) : HasVertexRails G 3 := by
  classical
  induction e using Sym2.ind with
  | _ x y =>
    have hadj : G.Adj x y := a.adj_of_mem_edges hea
    have hxa : x ∈ a.support := a.fst_mem_support_of_mem_edges hea
    have hya : y ∈ a.support := a.snd_mem_support_of_mem_edges hea
    have hxb : x ∈ b.support := b.fst_mem_support_of_mem_edges heb
    have hyb : y ∈ b.support := b.snd_mem_support_of_mem_edges heb
    have key : ∀ P : G.Walk x y, P.IsPath → g ∈ P.edges → HasVertexRails G 3 := by
      intro P hPp hgP
      obtain ⟨A, B, R, hR, hA, hB, hgR, hRc⟩ :=
        exists_subpath_avoiding {z : V | z ∈ a.support} g P.length P le_rfl hPp hxa hya hgP
      have hAB : A ≠ B := by
        rintro rfl
        rw [Walk.isPath_iff_nil] at hR
        rw [hR.eq_nil] at hgR
        simp at hgR
      exact hasVertexRails_three_of_theta ha hA hB hAB hR hRc hgR hga
    obtain ⟨p, q, hp, hq, -, -, -, -, -, -, hcov⟩ := exists_arcs_of_isCycle hb hxb hyb hadj.ne
    rcases hcov g hgb with hgp | hgq
    · exact key p hp hgp
    · exact key q hq hgq

/-- The fundamental cycle of an edge outside a spanning forest: it consists of that edge together
with forest edges.  (Digest §T2 Step 2.) -/
theorem exists_fundamental_cycle {V : Type*} {G F : SimpleGraph V} (hFG : F ≤ G)
    (hreach : F.Reachable = G.Reachable) {f : Sym2 V} (hfG : f ∈ G.edgeSet)
    (hfF : f ∉ F.edgeSet) :
    ∃ (w : V) (cf : G.Walk w w), cf.IsCycle ∧ f ∈ cf.edges ∧
      ∀ e ∈ cf.edges, e ≠ f → e ∈ F.edgeSet := by
  classical
  induction f using Sym2.ind with
  | _ x y =>
    have hadj : G.Adj x y := hfG
    obtain ⟨W⟩ : F.Reachable x y := by rw [hreach]; exact hadj.reachable
    have hWp : W.bypass.IsPath := W.bypass_isPath
    have hWF : ∀ e ∈ W.bypass.edges, e ∈ F.edgeSet := fun e he ↦
      W.bypass.edges_subset_edgeSet he
    have hsub : ∀ e ∈ W.bypass.edges, e ∈ G.edgeSet := fun e he ↦ edgeSet_mono hFG (hWF e he)
    have hE : (W.bypass.transfer G hsub).edges = W.bypass.edges := W.bypass.edges_transfer hsub
    have hswap : s(y, x) = s(x, y) := Sym2.eq_swap
    refine ⟨y, Walk.cons hadj.symm (W.bypass.transfer G hsub), ?_, ?_, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      refine ⟨hWp.transfer hsub, fun hcon ↦ hfF ?_⟩
      rw [hE] at hcon
      rw [← hswap]
      exact hWF _ hcon
    · rw [Walk.edges_cons, hswap]
      exact List.mem_cons_self
    · intro e he hef
      rw [Walk.edges_cons, List.mem_cons, hE] at he
      rcases he with rfl | he
      · exact absurd hswap hef
      · exact hWF e he

/-- **Bártfai 1960.**  A finite graph on `N ≥ 3` vertices with more than `3(N-1)/2` edges has two
vertices joined by three internally disjoint paths. -/
theorem hasVertexRails_three_of_edges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : 3 * (Fintype.card V - 1) / 2 + 1 ≤ G.edgeSet.ncard) (hV : 3 ≤ Fintype.card V) :
    HasVertexRails G 3 := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨F, hFG, hFac, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  obtain ⟨T, hFT, -, hTac, hTreach⟩ :=
    (⊤ : SimpleGraph V).exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic le_top hFac
  have hTpre : T.Preconnected := by
    intro x y
    rw [hTreach]
    exact SimpleGraph.connected_top.preconnected x y
  have hTtree : T.IsTree := ⟨⟨hTpre⟩, hTac⟩
  have hTcard : Nat.card T.edgeSet + 1 = Nat.card V :=
    (SimpleGraph.isTree_iff_connected_and_card.mp hTtree).2
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hTcard
  have hFT' : F.edgeSet.ncard ≤ T.edgeSet.ncard :=
    Set.ncard_le_ncard (edgeSet_mono hFT) (Set.toFinite _)
  have hcoeG : G.edgeFinset.card = G.edgeSet.ncard :=
    (Set.ncard_eq_toFinset_card' G.edgeSet).symm
  have hcoeF : F.edgeFinset.card = F.edgeSet.ncard :=
    (Set.ncard_eq_toFinset_card' F.edgeSet).symm
  have hFsub : F.edgeFinset ⊆ G.edgeFinset := edgeFinset_mono hFG
  have hQcard : (G.edgeFinset \ F.edgeFinset).card + F.edgeFinset.card = G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card hFsub
  have key : ∀ f : Sym2 V, ∃ (w : V) (cf : G.Walk w w), f ∈ G.edgeFinset \ F.edgeFinset →
      cf.IsCycle ∧ f ∈ cf.edges ∧ ∀ e ∈ cf.edges, e ≠ f → e ∈ F.edgeSet := by
    intro f
    by_cases hf : f ∈ G.edgeFinset \ F.edgeFinset
    · rw [Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset] at hf
      obtain ⟨w, cf, h1, h2, h3⟩ := exists_fundamental_cycle hFG hreach hf.1 hf.2
      exact ⟨w, cf, fun _ ↦ ⟨h1, h2, h3⟩⟩
    · obtain ⟨w0⟩ := hne
      exact ⟨w0, Walk.nil, fun hcon ↦ absurd hcon hf⟩
  choose cw cwalk cprop using key
  by_cases hdis : ∀ f ∈ G.edgeFinset \ F.edgeFinset, ∀ g ∈ G.edgeFinset \ F.edgeFinset, f ≠ g →
      Disjoint (cwalk f).edges.toFinset (cwalk g).edges.toFinset
  · exfalso
    have hcard3 : ∀ f ∈ G.edgeFinset \ F.edgeFinset, 3 ≤ (cwalk f).edges.toFinset.card := by
      intro f hf
      obtain ⟨hcyc, -, -⟩ := cprop f hf
      rw [List.toFinset_card_of_nodup hcyc.isTrail.edges_nodup, Walk.length_edges]
      exact hcyc.three_le_length
    have hbi : ((G.edgeFinset \ F.edgeFinset).biUnion
        fun f ↦ (cwalk f).edges.toFinset).card =
        ∑ f ∈ G.edgeFinset \ F.edgeFinset, (cwalk f).edges.toFinset.card :=
      Finset.card_biUnion hdis
    have hsub : ((G.edgeFinset \ F.edgeFinset).biUnion
        fun f ↦ (cwalk f).edges.toFinset) ⊆ G.edgeFinset := by
      intro e he
      rw [Finset.mem_biUnion] at he
      obtain ⟨f, -, hef⟩ := he
      rw [List.mem_toFinset] at hef
      rw [mem_edgeFinset]
      exact (cwalk f).edges_subset_edgeSet hef
    have hsum : (G.edgeFinset \ F.edgeFinset).card * 3 ≤
        ∑ f ∈ G.edgeFinset \ F.edgeFinset, (cwalk f).edges.toFinset.card := by
      simpa using Finset.card_nsmul_le_sum (G.edgeFinset \ F.edgeFinset)
        (fun f ↦ (cwalk f).edges.toFinset.card) 3 hcard3
    have hle : ∑ f ∈ G.edgeFinset \ F.edgeFinset, (cwalk f).edges.toFinset.card ≤
        G.edgeFinset.card := hbi ▸ Finset.card_le_card hsub
    omega
  · push Not at hdis
    obtain ⟨f, hf, g, hg, hfg, hnd⟩ := hdis
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨e, hef, heg⟩ := hnd
    obtain ⟨hcf, -, hfsub⟩ := cprop f hf
    obtain ⟨hcg, hgmem, -⟩ := cprop g hg
    have hgna : g ∉ (cwalk f).edges := by
      intro hcon
      rcases eq_or_ne g f with rfl | hne'
      · exact hfg rfl
      · exact (Finset.mem_sdiff.mp hg).2 (by rw [mem_edgeFinset]; exact hfsub g hcon hne')
    exact hasVertexRails_three_of_cycles hcf hcg (List.mem_toFinset.mp hef)
      (List.mem_toFinset.mp heg) hgmem hgna

/-- The Bollobás–Erdős conjecture for `m = 3`, vertex-disjoint reading: a graph with
`1 + 2n` vertices and `1 + 3n` edges has two vertices joined by three internally disjoint
paths. -/
theorem vertex_rails_three {n : ℕ} (hn : 1 ≤ n) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (3 - 1)) (hE : G.edgeSet.ncard = 1 + n * Nat.choose 3 2) :
    HasVertexRails G 3 := by
  have h32 : Nat.choose 3 2 = 3 := by decide
  rw [h32] at hE
  exact hasVertexRails_three_of_edges G (by omega) (by omega)

end Erdos915
