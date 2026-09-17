import MerLeanExperiment.RailsTwo

/-!
# Erdős #915 for `m = 4`: Bollobás' theorem `k₄(N) = 2N − 1`

Bollobás (*On graphs with at most three independent paths connecting any two vertices*, Studia
Sci. Math. Hungar. **1** (1966) 137–140) proved that a graph on `N ≥ 4` vertices with `2N − 1`
edges always has two vertices joined by four internally disjoint paths.

The file is organised as follows.

* **Transport.** Rails only grow when the graph grows, and a path avoiding a vertex `w` survives
  the deletion of `w`.
* **Suppression of a degree-three vertex.** If `x` is adjacent to `a` and `b`, every rail of
  `(G − x) + ab` lifts to a rail of `G` by replacing `ab` with the detour `a–x–b`.
* **Splitting at a cut vertex.** A vertex set `A` whose only edges to the outside emanate from a
  single vertex `a ∈ A` splits `G` into two edge-disjoint subgraphs.
* **The induction.** A graph without a `4`-rail on `N ≥ 1` vertices has at most `2N − 2` edges.
-/

namespace Erdos915

open SimpleGraph Finset

section Transport

variable {V : Type*} {G H : SimpleGraph V}

/-- Rails are monotone in the graph. -/
theorem hasVertexRails_mono {m : ℕ} (hGH : G ≤ H) (h : HasVertexRails G m) :
    HasVertexRails H m := by
  obtain ⟨u, v, huv, p, hinj, hpath, hdisj⟩ := h
  have hedge : ∀ i : Fin m, ∀ e ∈ (p i).edges, e ∈ H.edgeSet := fun i e he ↦
    edgeSet_mono hGH ((p i).edges_subset_edgeSet he)
  refine ⟨u, v, huv, fun i ↦ (p i).transfer H (hedge i), ?_,
    fun i ↦ (hpath i).transfer _, ?_⟩
  · intro i j hij
    exact hinj (Walk.ext_support (by
      have := Walk.support_transfer (p i) (hedge i)
      have := Walk.support_transfer (p j) (hedge j)
      simp_all))
  · intro i j hij w hwi hwj
    rw [Walk.support_transfer] at hwi hwj
    exact hdisj i j hij w hwi hwj

/-- A vertex with no neighbours does not occur on a walk that does not start there. -/
theorem notMem_support_of_forall_not_adj {v w : V} (hiso : ∀ z, ¬ G.Adj w z) :
    ∀ {u : V} (p : G.Walk u v), u ≠ w → w ∉ p.support := by
  intro u p
  induction p with
  | nil => exact fun hu ↦ by simpa using fun h ↦ hu h.symm
  | @cons a y _ hadj q ih =>
    refine fun hu ↦ ?_
    have hyw : y ≠ w := fun h ↦ hiso a (h ▸ hadj.symm)
    simpa using ⟨fun h ↦ hu h.symm, ih hyw⟩

/-- A walk avoiding `w` gives reachability after deleting the incidence set of `w`. -/
theorem reachable_deleteIncidenceSet_of_notMem_support {u v w : V} (p : G.Walk u v)
    (hw : w ∉ p.support) : (G.deleteIncidenceSet w).Reachable u v := by
  refine ⟨p.transfer _ fun e he ↦ ?_⟩
  induction e using Sym2.ind with
  | _ y z =>
    have hyz : G.Adj y z := p.adj_of_mem_edges he
    have hy : y ≠ w := fun h ↦ hw (h ▸ Walk.fst_mem_support_of_mem_edges p he)
    have hz : z ≠ w := fun h ↦ hw (h ▸ Walk.snd_mem_support_of_mem_edges p he)
    simpa [deleteIncidenceSet_adj] using ⟨hyz, hy, hz⟩

/-- A path between distinct endpoints whose support consists of endpoints only is the edge. -/
theorem support_eq_pair_of_subset {u v : V} {p : G.Walk u v} (hp : p.IsPath) (huv : u ≠ v)
    (hs : ∀ w ∈ p.support, w = u ∨ w = v) : p.support = [u, v] := by
  classical
  have hsub : p.support.toFinset ⊆ {u, v} := by
    intro w hw
    simp only [List.mem_toFinset] at hw
    simpa using hs w hw
  have hlen : p.support.length ≤ 2 := by
    rw [← List.toFinset_card_of_nodup hp.support_nodup]
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  have h2 : 2 ≤ p.support.length := by
    by_contra h
    rw [not_le, Walk.length_support] at h
    exact huv (Walk.eq_of_length_eq_zero (p := p) (by omega))
  obtain ⟨y, z, hyz⟩ := List.length_eq_two.mp (le_antisymm hlen h2)
  have hy : y = u := by
    have h := p.cons_tail_support
    rw [hyz] at h
    simpa using h.symm
  subst hy
  have hz : z = v := by
    have hv := p.end_mem_support
    rw [hyz] at hv
    rcases List.mem_cons.mp hv with h | h
    · exact absurd h.symm huv
    · exact (List.mem_singleton.mp h).symm
  rw [hyz, hz]

end Transport


section Suppress

variable {V : Type*} {G : SimpleGraph V} {x a b : V}

/-- In `(G − x) + ab` every edge is either the new edge `ab` or an edge of `G`. -/
theorem eq_or_mem_edgeSet_of_mem_sup_edge {e : Sym2 V}
    (he : e ∈ ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).edgeSet) :
    e = s(a, b) ∨ e ∈ G.edgeSet := by
  induction e using Sym2.ind with
  | _ y z =>
    simp only [mem_edgeSet, sup_adj, deleteIncidenceSet_adj, edge_adj] at he
    rcases he with ⟨h, -, -⟩ | ⟨h | h, -⟩
    · exact Or.inr h
    · exact Or.inl (by rw [h.1, h.2])
    · exact Or.inl (by rw [h.1, h.2]; exact Sym2.eq_swap)

/-- The detour step: a path of `(G − x) + ab` that splits at an occurrence of the new edge,
traversed from `c` to `d`, is lifted to a path of `G` through `x`. -/
theorem exists_lift_of_decomp {u v c d : V} (hxc : G.Adj x c) (hxd : G.Adj x d)
    {p : ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).Walk u v} (hp : p.IsPath)
    (hx : x ∉ p.support) {hcd : ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).Adj c d}
    (ru : ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).Walk u c)
    (rv : ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).Walk d v)
    (hdec : p = (ru.append hcd.toWalk).append rv) (hcdab : s(c, d) = s(a, b)) :
    ∃ q : G.Walk u v, q.IsPath ∧ (∀ w ∈ q.support, w ∈ p.support ∨ w = x) ∧
      (∀ w ∈ p.support, w ∈ q.support) ∧ (x ∈ q.support → s(a, b) ∈ p.edges) := by
  have hedges : p.edges = (ru.edges ++ [s(c, d)]) ++ rv.edges := by
    rw [hdec, Walk.edges_append, Walk.edges_append, hcd.edges_toWalk]
  have hnd : p.edges.Nodup := hp.edges_nodup
  rw [hedges] at hnd
  have hcdru : s(c, d) ∉ ru.edges := fun h ↦
    (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 _ h _ (by simp) rfl
  have hcdrv : s(c, d) ∉ rv.edges := fun h ↦
    (List.nodup_append.mp hnd).2.2 _ (by simp) _ h rfl
  have hru : ∀ e ∈ ru.edges, e ∈ G.edgeSet := by
    intro e he
    rcases eq_or_mem_edgeSet_of_mem_sup_edge (ru.edges_subset_edgeSet he) with h | h
    · exact absurd (by rw [hcdab, ← h]; exact he) hcdru
    · exact h
  have hrv : ∀ e ∈ rv.edges, e ∈ G.edgeSet := by
    intro e he
    rcases eq_or_mem_edgeSet_of_mem_sup_edge (rv.edges_subset_edgeSet he) with h | h
    · exact absurd (by rw [hcdab, ← h]; exact he) hcdrv
    · exact h
  refine ⟨((ru.transfer G hru).append (Walk.cons hxc.symm (Walk.cons hxd Walk.nil))).append
    (rv.transfer G hrv), ?_, ?_, ?_, ?_⟩
  · rw [Walk.isPath_def]
    have hq : (((ru.transfer G hru).append (Walk.cons hxc.symm (Walk.cons hxd Walk.nil))).append
        (rv.transfer G hrv)).support = ru.support ++ x :: d :: rv.support.tail := by
      simp [Walk.support_append, Walk.support_transfer]
    have hps : p.support = ru.support ++ d :: rv.support.tail := by
      rw [hdec]; simp [Walk.support_append]
    rw [hq, List.nodup_middle]
    rw [hps] at hx
    exact List.nodup_cons.mpr ⟨hx, hps ▸ hp.support_nodup⟩
  · intro w hw
    have hq : (((ru.transfer G hru).append (Walk.cons hxc.symm (Walk.cons hxd Walk.nil))).append
        (rv.transfer G hrv)).support = ru.support ++ x :: d :: rv.support.tail := by
      simp [Walk.support_append, Walk.support_transfer]
    have hps : p.support = ru.support ++ d :: rv.support.tail := by
      rw [hdec]; simp [Walk.support_append]
    rw [hq] at hw
    rw [hps]
    simp only [List.mem_append, List.mem_cons] at hw ⊢
    tauto
  · intro w hw
    have hq : (((ru.transfer G hru).append (Walk.cons hxc.symm (Walk.cons hxd Walk.nil))).append
        (rv.transfer G hrv)).support = ru.support ++ x :: d :: rv.support.tail := by
      simp [Walk.support_append, Walk.support_transfer]
    have hps : p.support = ru.support ++ d :: rv.support.tail := by
      rw [hdec]; simp [Walk.support_append]
    rw [hps] at hw
    rw [hq]
    simp only [List.mem_append, List.mem_cons] at hw ⊢
    tauto
  · intro _
    rw [hedges, ← hcdab]
    simp

/-- Lifting a path of `(G − x) + ab` to a path of `G`, detouring through `x` if the new edge is
used. -/
theorem exists_lift_path (hxa : G.Adj x a) (hxb : G.Adj x b) (hne : a ≠ b) {u v : V}
    {p : ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).Walk u v} (hp : p.IsPath)
    (hx : x ∉ p.support) :
    ∃ q : G.Walk u v, q.IsPath ∧ (∀ w ∈ q.support, w ∈ p.support ∨ w = x) ∧
      (∀ w ∈ p.support, w ∈ q.support) ∧ (x ∈ q.support → s(a, b) ∈ p.edges) := by
  by_cases hmem : s(a, b) ∈ p.edges
  · have hab : ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).Adj a b :=
      Or.inr (by simpa [edge_adj] using hne)
    rcases (Walk.isSubwalk_toWalk_iff_mem_edges hab).mpr hmem with h | h
    · obtain ⟨ru, rv, hdec⟩ := h
      exact exists_lift_of_decomp hxa hxb hp hx ru rv hdec rfl
    · obtain ⟨ru, rv, hdec⟩ := h
      exact exists_lift_of_decomp hxb hxa hp hx ru rv hdec Sym2.eq_swap
  · have hpe : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      rcases eq_or_mem_edgeSet_of_mem_sup_edge (p.edges_subset_edgeSet he) with h | h
      · exact absurd (h ▸ he) hmem
      · exact h
    exact ⟨p.transfer G hpe, hp.transfer hpe,
      fun w hw ↦ Or.inl (by rwa [Walk.support_transfer] at hw),
      fun w hw ↦ by rwa [Walk.support_transfer],
      fun hxq ↦ absurd (by rwa [Walk.support_transfer] at hxq) hx⟩

/-- **Suppression of a degree-three vertex.**  If `x` is adjacent to both `a` and `b`, every rail
of the graph obtained by deleting `x` and adding the edge `ab` lifts to a rail of `G`: at most one
of the paths can use the new edge, and that one is rerouted through `x`. -/
theorem hasVertexRails_of_sup_edge (hxa : G.Adj x a) (hxb : G.Adj x b) (hne : a ≠ b) {m : ℕ}
    (hm : 0 < m) (h : HasVertexRails ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b) m) :
    HasVertexRails G m := by
  obtain ⟨u, v, huv, p, hinj, hpath, hdisj⟩ := h
  have hiso : ∀ z, ¬ ((G.deleteIncidenceSet x) ⊔ SimpleGraph.edge a b).Adj x z := by
    intro z hz
    rcases hz with hz | hz
    · exact (deleteIncidenceSet_adj.mp hz).2.1 rfl
    · rcases (edge_adj ..).mp hz with ⟨h1 | h1, -⟩
      · exact hxa.ne h1.1
      · exact hxb.ne h1.1
  have hux : u ≠ x := by
    rintro rfl
    have hnil : ¬ (p ⟨0, hm⟩).Nil := fun hn ↦
      huv (Walk.eq_of_length_eq_zero (Walk.length_eq_zero_iff.mpr hn))
    exact hiso _ (Walk.adj_snd hnil)
  have hx : ∀ i, x ∉ (p i).support := fun i ↦
    notMem_support_of_forall_not_adj hiso (p i) hux
  choose q hq1 hq2 hq3 hq4 using fun i ↦ exists_lift_path hxa hxb hne (hpath i) (hx i)
  have hqdisj : ∀ i j, i ≠ j → InternallyDisjoint (q i) (q j) := by
    intro i j hij w hwi hwj
    by_cases hwx : w = x
    · subst hwx
      exfalso
      have e1 := hq4 i hwi
      have e2 := hq4 j hwj
      have ha := hdisj i j hij a (Walk.fst_mem_support_of_mem_edges _ e1)
        (Walk.fst_mem_support_of_mem_edges _ e2)
      have hb := hdisj i j hij b (Walk.snd_mem_support_of_mem_edges _ e1)
        (Walk.snd_mem_support_of_mem_edges _ e2)
      have hsym : s(a, b) = s(u, v) := by
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;>
          first
            | rfl
            | exact Sym2.eq_swap
            | exact absurd rfl hne
      rw [hsym] at e1 e2
      have hadj := (p i).adj_of_mem_edges e1
      exact hij (hinj ((eq_cons_nil_of_mem_edges (hpath i) hadj e1).trans
        (eq_cons_nil_of_mem_edges (hpath j) hadj e2).symm))
    · rcases hq2 i w hwi with h1 | h1
      · rcases hq2 j w hwj with h2 | h2
        · exact hdisj i j hij w h1 h2
        · exact absurd h2 hwx
      · exact absurd h1 hwx
  refine ⟨u, v, huv, q, ?_, hq1, hqdisj⟩
  intro i j hqij
  by_contra hij
  have hsub : ∀ w ∈ (q i).support, w = u ∨ w = v := fun w hw ↦
    hqdisj i j hij w hw (hqij ▸ hw)
  have hpi : (p i).support = [u, v] :=
    support_eq_pair_of_subset (hpath i) huv fun w hw ↦ hsub w (hq3 i w hw)
  have hpj : (p j).support = [u, v] :=
    support_eq_pair_of_subset (hpath j) huv fun w hw ↦ hsub w (hqij ▸ hq3 j w hw)
  exact hij (hinj (Walk.ext_support (hpi.trans hpj.symm)))

end Suppress



section Counting

/-- The edge set as a `Finset`, counted by `Set.ncard`. -/
theorem ncard_edgeSet_eq_card_edgeFinset {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset :=
  Set.ncard_eq_toFinset_card' _

/-- A vertex outside the support set has degree zero. -/
theorem degree_eq_zero_of_notMem {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {s : Finset V} (hs : ∀ u v : V, G.Adj u v → u ∈ s) {w : V} (hw : w ∉ s) :
    G.degree w = 0 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero]
  exact Finset.eq_empty_of_forall_notMem fun z hz ↦ hw (hs w z (by simpa using hz))

/-- The degree-sum formula, restricted to the support set. -/
theorem sum_degree_eq_two_mul {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset V} (hs : ∀ u v : V, G.Adj u v → u ∈ s) :
    ∑ w ∈ s, G.degree w = 2 * G.edgeSet.ncard := by
  rw [ncard_edgeSet_eq_card_edgeFinset, ← G.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_subset (Finset.subset_univ s) fun w _ hw ↦ degree_eq_zero_of_notMem hs hw

/-- Degrees are bounded by the size of the support set. -/
theorem degree_le_card_sub_one {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset V} (hs : ∀ u v : V, G.Adj u v → u ∈ s) {w : V} :
    G.degree w ≤ s.card - 1 := by
  by_cases hw : w ∈ s
  · rw [← card_neighborFinset_eq_degree, ← Finset.card_erase_of_mem hw]
    refine Finset.card_le_card fun z hz ↦ ?_
    have hadj : G.Adj w z := by simpa using hz
    exact Finset.mem_erase.mpr ⟨hadj.ne', hs z w hadj.symm⟩
  · simp [degree_eq_zero_of_notMem hs hw]

/-- A graph whose edges lie inside `s` has at most `|s|(|s| − 1)/2` edges. -/
theorem two_mul_ncard_edgeSet_le {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {s : Finset V} (hs : ∀ u v : V, G.Adj u v → u ∈ s) :
    2 * G.edgeSet.ncard ≤ s.card * (s.card - 1) := by
  rw [← sum_degree_eq_two_mul hs]
  calc ∑ w ∈ s, G.degree w ≤ ∑ _w ∈ s, (s.card - 1) :=
        Finset.sum_le_sum fun w _ ↦ degree_le_card_sub_one hs
    _ = s.card * (s.card - 1) := by rw [Finset.sum_const, smul_eq_mul]

/-- Every graph has a subgraph with any prescribed smaller number of edges. -/
theorem exists_le_ncard_edgeSet_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] {k : ℕ} (hk : k ≤ G.edgeSet.ncard) :
    ∃ K : SimpleGraph V, K ≤ G ∧ K.edgeSet.ncard = k := by
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (show k ≤ #G.edgeFinset from (ncard_edgeSet_eq_card_edgeFinset G) ▸ hk)
  have hTe : (↑T : Set (Sym2 V)) ⊆ G.edgeSet := fun e he ↦
    mem_edgeFinset.mp (hTsub (by simpa using he))
  refine ⟨fromEdgeSet (↑T : Set (Sym2 V)), ?_, ?_⟩
  · have hle := fromEdgeSet_mono hTe
    rwa [fromEdgeSet_edgeSet] at hle
  · have hset : (fromEdgeSet (↑T : Set (Sym2 V))).edgeSet = (↑T : Set (Sym2 V)) := by
      rw [edgeSet_fromEdgeSet]
      ext e
      simp only [Set.mem_sdiff, and_iff_left_iff_imp]
      exact fun he hd ↦ G.not_isDiag_of_mem_edgeSet (hTe he) (Sym2.mem_diagSet.mp hd)
    rw [hset, Set.ncard_coe_finset, hTcard]

end Counting

section Split

/-- **Splitting at a cut vertex.**  If `a ∈ A` is the only vertex of `A` with edges leaving `A`,
then the edges of `G` split into those inside `A` and the rest, and each part spans a subgraph. -/
theorem exists_split {V : Type*} (G : SimpleGraph V) (A : Set V) (a : V)
    (hcut : ∀ u v : V, G.Adj u v → u ∈ A → u ≠ a → v ∈ A) :
    ∃ G₁ G₂ : SimpleGraph V, G₁ ≤ G ∧ G₂ ≤ G ∧
      (∀ u v : V, G₁.Adj u v → u ∈ A) ∧
      (∀ u v : V, G₂.Adj u v → u ∉ A ∨ u = a) ∧
      G.edgeSet = G₁.edgeSet ∪ G₂.edgeSet ∧ Disjoint G₁.edgeSet G₂.edgeSet := by
  classical
  refine ⟨G.deleteEdges {e : Sym2 V | ¬ ∀ y ∈ e, y ∈ A},
    G.deleteEdges {e : Sym2 V | ∀ y ∈ e, y ∈ A}, deleteEdges_le _, deleteEdges_le _, ?_, ?_,
    ?_, ?_⟩
  · intro u v huv
    have h := (deleteEdges_adj.mp huv).2
    simp only [Set.mem_ofPred_eq, not_not] at h
    exact h u (by simp)
  · intro u v huv
    obtain ⟨hadj, h⟩ := deleteEdges_adj.mp huv
    simp only [Set.mem_ofPred_eq] at h
    by_contra hcon
    push Not at hcon
    refine h fun y hy ↦ ?_
    rcases Sym2.mem_iff.mp hy with rfl | rfl
    · exact hcon.1
    · exact hcut u y hadj hcon.1 hcon.2
  · rw [edgeSet_deleteEdges, edgeSet_deleteEdges]
    ext e
    constructor
    · intro he
      by_cases hP : ∀ y ∈ e, y ∈ A
      · exact Or.inl ⟨he, by simpa using hP⟩
      · exact Or.inr ⟨he, hP⟩
    · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
  · rw [edgeSet_deleteEdges, edgeSet_deleteEdges, Set.disjoint_left]
    rintro e ⟨-, hne⟩ ⟨-, hne2⟩
    simp only [Set.mem_ofPred_eq, not_not] at hne
    exact hne2 hne

end Split

section Wheel

/-- **The four paths.**  If `{x, a, b, c}` spans a `K₄` in `K` and `L` is a subgraph of `K` in
which `x` and `c` are isolated and `a` is not adjacent to `b`, then any `L`-path from `a` to `b`
completes the three paths `a–b`, `a–c–b`, `a–x–b` to a `4`-rail of `K`. -/
theorem hasVertexRails_four_of_detour {V : Type*} {K : SimpleGraph V} {x a b c : V}
    (hxa : K.Adj x a) (hxb : K.Adj x b) (hxc : K.Adj x c) (hab : K.Adj a b) (hac : K.Adj a c)
    (hbc : K.Adj b c) {L : SimpleGraph V} (hLK : L ≤ K) (hLx : ∀ z, ¬ L.Adj x z)
    (hLc : ∀ z, ¬ L.Adj c z) (hLab : ¬ L.Adj a b) (hreach : L.Reachable a b) :
    HasVertexRails K 4 := by
  classical
  refine hreach.elim_path fun W ↦ ?_
  have hax : a ≠ x := hxa.ne'
  have hbx : b ≠ x := hxb.ne'
  have hcx : c ≠ x := hxc.ne'
  have hac' : a ≠ c := hac.ne
  have hbc' : b ≠ c := hbc.ne
  have hab' : a ≠ b := hab.ne
  have hcb : c ≠ b := hbc.ne'
  have hxb' : x ≠ b := hxb.ne
  have hWx : x ∉ W.val.support := notMem_support_of_forall_not_adj hLx _ hax
  have hWc : c ∉ W.val.support := notMem_support_of_forall_not_adj hLc _ hac'
  have hWe : ∀ e ∈ W.val.edges, e ∈ K.edgeSet := fun e he ↦
    edgeSet_mono hLK (W.val.edges_subset_edgeSet he)
  have hWab : s(a, b) ∉ W.val.edges := fun he ↦ hLab (W.val.adj_of_mem_edges he)
  obtain ⟨P, hPs, hPe, hPp⟩ : ∃ P : K.Walk a b, P.support = W.val.support ∧
      P.edges = W.val.edges ∧ P.IsPath :=
    ⟨W.val.transfer K hWe, Walk.support_transfer _ _, Walk.edges_transfer _ _,
      W.property.transfer hWe⟩
  obtain ⟨w0, hw0s, hw0e, hw0p⟩ : ∃ w0 : K.Walk a b, w0.support = [a, b] ∧
      w0.edges = [s(a, b)] ∧ w0.IsPath := ⟨hab.toWalk, by simp, by simp, by simp [hab']⟩
  obtain ⟨w1, hw1s, hw1p⟩ : ∃ w1 : K.Walk a b, w1.support = [a, c, b] ∧ w1.IsPath :=
    ⟨Walk.cons hac (Walk.cons hbc.symm Walk.nil), by simp,
      by simp [Walk.cons_isPath_iff, hac', hab', hcb]⟩
  obtain ⟨w2, hw2s, hw2p⟩ : ∃ w2 : K.Walk a b, w2.support = [a, x, b] ∧ w2.IsPath :=
    ⟨Walk.cons hxa.symm (Walk.cons hxb Walk.nil), by simp,
      by simp [Walk.cons_isPath_iff, hax, hab', hxb']⟩
  have hpaths : ∀ i : Fin 4, (![w0, w1, w2, P] i).IsPath := by
    intro i; fin_cases i <;> simpa using ‹_›
  have hdisj : ∀ i j : Fin 4, i ≠ j → InternallyDisjoint (![w0, w1, w2, P] i)
      (![w0, w1, w2, P] j) := by
    intro i j hij w hwi hwj
    fin_cases i <;> fin_cases j <;> simp_all <;> grind
  have hone : ∀ k : Fin 4, (![w0, w1, w2, P] k).support = [a, b] → k = 0 := by
    intro k hk
    fin_cases k
    · rfl
    · exfalso
      have h1 : w1.support = [a, b] := by simpa using hk
      rw [hw1s] at h1
      simp at h1
    · exfalso
      have h2 : w2.support = [a, b] := by simpa using hk
      rw [hw2s] at h2
      simp at h2
    · refine absurd ?_ hWab
      have hPsab : P.support = [a, b] := by simpa using hk
      have : P = w0 := Walk.ext_support (by rw [hPsab, hw0s])
      rw [← hPe, this, hw0e]
      simp
  refine ⟨a, b, hab', ![w0, w1, w2, P], ?_, hpaths, hdisj⟩
  intro i j hijeq
  by_contra hij
  have hsub : ∀ w ∈ (![w0, w1, w2, P] i).support, w = a ∨ w = b := fun w hw ↦
    hdisj i j hij w hw (hijeq ▸ hw)
  have hpi : (![w0, w1, w2, P] i).support = [a, b] :=
    support_eq_pair_of_subset (hpaths i) hab' hsub
  exact hij ((hone i hpi).trans (hone j (by rw [← hijeq]; exact hpi)).symm)

end Wheel


section Reachability

variable {V : Type*} {G : SimpleGraph V}

/-- An isolated vertex is reachable from nothing else. -/
theorem not_reachable_of_isolated {p z : V} (hiso : ∀ y, ¬ G.Adj z y) (hpz : p ≠ z) :
    ¬ G.Reachable p z := fun h ↦
  h.elim fun W ↦ notMem_support_of_forall_not_adj hiso W hpz W.end_mem_support

/-- On a path, the initial segment and the final segment meet only at the splitting vertex. -/
theorem notMem_support_dropUntil [DecidableEq V] {u v w z : V} {W : G.Walk u v} (hW : W.IsPath)
    (hmem : w ∈ W.support) (hz : z ∈ (W.takeUntil w hmem).support) (hzw : z ≠ w) :
    z ∉ (W.dropUntil w hmem).support := by
  have hsupp : W.support =
      (W.takeUntil w hmem).support ++ (W.dropUntil w hmem).support.tail := by
    conv_lhs => rw [← W.take_spec hmem]
    rw [Walk.support_append]
  have hnd : W.support.Nodup := hW.support_nodup
  rw [hsupp] at hnd
  have hdisj := (List.nodup_append.mp hnd).2.2
  have htail : z ∉ (W.dropUntil w hmem).support.tail := fun h ↦ hdisj z hz z h rfl
  intro hcon
  rw [← (W.dropUntil w hmem).cons_tail_support] at hcon
  rcases List.mem_cons.mp hcon with h | h
  · exact hzw h
  · exact htail h

/-- If `u` and `v` are separated by deleting `w`, and `w` and `v` are separated by deleting `u`,
then `u` and `v` are not connected at all. -/
theorem not_reachable_of_pair [DecidableEq V] {u v w : V} (huw : u ≠ w)
    (h1 : ¬ (G.deleteIncidenceSet w).Reachable u v)
    (h2 : ¬ (G.deleteIncidenceSet u).Reachable w v) : ¬ G.Reachable u v := by
  intro h
  refine h.elim_path fun W ↦ ?_
  by_cases hmem : w ∈ W.val.support
  · refine h2 ?_
    refine reachable_deleteIncidenceSet_of_notMem_support (W.val.dropUntil w hmem) ?_
    exact notMem_support_dropUntil W.property hmem (Walk.start_mem_support _) huw
  · exact h1 (reachable_deleteIncidenceSet_of_notMem_support W.val hmem)

end Reachability

section Induction

/-- The inductive hypothesis at size `n`: the edge bound for all smaller support sets. -/
def RailBoundBelow (V : Type*) [Fintype V] (n : ℕ) : Prop :=
  ∀ (t : Finset V) (K : SimpleGraph V), t.card < n → t.Nonempty →
    (∀ u v : V, K.Adj u v → u ∈ t) → ¬ HasVertexRails K 4 →
      K.edgeSet.ncard + 2 ≤ 2 * t.card

/-- Deleting a vertex removes exactly its degree many edges. -/
theorem ncard_edgeSet_deleteIncidenceSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeSet.ncard + G.degree x = G.edgeSet.ncard := by
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  show #(G.deleteIncidenceSet x).edgeFinset + G.degree x = #G.edgeFinset
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff, ← card_incidenceFinset_eq_degree]
  exact Finset.card_sdiff_add_card_eq_card (incidenceFinset_subset G x)

/-- The splitting step of the induction. -/
theorem le_of_split {V : Type*} [Fintype V] {n : ℕ} (ih : RailBoundBelow V n)
    {s s₁ s₂ : Finset V} {G : SimpleGraph V} (hs : ∀ u v : V, G.Adj u v → u ∈ s)
    (hcard : s.card = n) (hrail : ¬ HasVertexRails G 4) (A : Set V) (a : V)
    (hcut : ∀ u v : V, G.Adj u v → u ∈ A → u ≠ a → v ∈ A)
    (hs₁ : ∀ w : V, w ∈ s → w ∈ A → w ∈ s₁)
    (hs₂ : ∀ w : V, w ∈ s → (w ∉ A ∨ w = a) → w ∈ s₂)
    (hsum : s₁.card + s₂.card ≤ s.card + 1) (hne₁ : s₁.Nonempty) (hne₂ : s₂.Nonempty)
    (hlt₁ : s₁.card < n) (hlt₂ : s₂.card < n) : G.edgeSet.ncard + 2 ≤ 2 * n := by
  obtain ⟨G₁, G₂, h1le, h2le, h1A, h2A, hunion, hdisj⟩ := exists_split G A a hcut
  have hb₁ := ih s₁ G₁ hlt₁ hne₁
    (fun u v huv ↦ hs₁ u (hs u v (h1le huv)) (h1A u v huv))
    (fun hr ↦ hrail (hasVertexRails_mono h1le hr))
  have hb₂ := ih s₂ G₂ hlt₂ hne₂
    (fun u v huv ↦ hs₂ u (hs u v (h2le huv)) (h2A u v huv))
    (fun hr ↦ hrail (hasVertexRails_mono h2le hr))
  have hcardeq : G.edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard := by
    rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  omega

/-- A cut vertex in a graph with `2n − 1` edges contradicts the inductive hypothesis. -/
theorem false_of_cut {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (ih : RailBoundBelow V n)
    {s : Finset V} {K : SimpleGraph V} (hs : ∀ u v : V, K.Adj u v → u ∈ s)
    (hcard : s.card = n) (hrail : ¬ HasVertexRails K 4)
    (hKcard : K.edgeSet.ncard + 1 = 2 * n) (A : Set V) (a : V) (haA : a ∈ A) (has : a ∈ s)
    (hcut : ∀ u v : V, K.Adj u v → u ∈ A → u ≠ a → v ∈ A)
    (hz : ∃ z ∈ s, z ∈ A ∧ z ≠ a) (hout : ∃ z ∈ s, z ∉ A) : False := by
  classical
  obtain ⟨z, hzs, hzA, hza⟩ := hz
  obtain ⟨y, hys, hyA⟩ := hout
  obtain ⟨s₁, hm₁⟩ : ∃ s₁ : Finset V, ∀ w : V, w ∈ s₁ ↔ w ∈ s ∧ w ∈ A :=
    ⟨s.filter (fun w ↦ w ∈ A), by simp⟩
  obtain ⟨s₂, hm₂⟩ : ∃ s₂ : Finset V, ∀ w : V, w ∈ s₂ ↔ (w ∈ s ∧ w ∉ A) ∨ w = a :=
    ⟨insert a (s.filter (fun w ↦ w ∉ A)), by intro w; simp; tauto⟩
  have hunion : s₁ ∪ s₂ = s := by
    ext w
    simp only [Finset.mem_union, hm₁, hm₂]
    constructor
    · rintro (⟨hw, -⟩ | ⟨hw, -⟩ | rfl)
      · exact hw
      · exact hw
      · exact has
    · intro hw
      by_cases hwA : w ∈ A
      · exact Or.inl ⟨hw, hwA⟩
      · exact Or.inr (Or.inl ⟨hw, hwA⟩)
  have hinter : s₁ ∩ s₂ = {a} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_singleton, hm₁, hm₂]
    constructor
    · rintro ⟨⟨-, hwA⟩, ⟨-, h⟩ | rfl⟩
      · exact absurd hwA h
      · rfl
    · rintro rfl
      exact ⟨⟨has, haA⟩, Or.inr rfl⟩
  have hcards : s₁.card + s₂.card = s.card + 1 := by
    have hcu := Finset.card_union_add_card_inter s₁ s₂
    rw [hunion, hinter] at hcu
    simpa using hcu.symm
  have h2le : 2 ≤ s₁.card := by
    have hsub : ({a, z} : Finset V) ⊆ s₁ := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (hm₁ w).mpr ⟨has, haA⟩
      · exact (hm₁ w).mpr ⟨(Finset.mem_singleton.mp hw) ▸ hzs,
          (Finset.mem_singleton.mp hw) ▸ hzA⟩
    have hle := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem (by simpa using fun h ↦ hza h.symm),
      Finset.card_singleton] at hle
  have hylt : s₁.card < s.card := by
    refine Finset.card_lt_card ⟨fun w hw ↦ ((hm₁ w).mp hw).1, fun hcon ↦ ?_⟩
    exact hyA ((hm₁ y).mp (hcon hys)).2
  have hbound := le_of_split ih hs hcard hrail A a hcut
    (fun w hw hwA ↦ (hm₁ w).mpr ⟨hw, hwA⟩)
    (fun w hw hwA ↦ (hm₂ w).mpr (hwA.imp (fun h ↦ ⟨hw, h⟩) id))
    (by omega) ⟨a, (hm₁ a).mpr ⟨has, haA⟩⟩ ⟨a, (hm₂ a).mpr (Or.inr rfl)⟩
    (by omega) (by omega)
  omega

/-- A degree-three vertex with two non-adjacent neighbours contradicts the bound. -/
theorem false_of_nonadj {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (ih : RailBoundBelow V n)
    {s : Finset V} {K : SimpleGraph V} [DecidableRel K.Adj]
    (hs : ∀ u v : V, K.Adj u v → u ∈ s) (hcard : s.card = n)
    (hrail : ¬ HasVertexRails K 4) (hKcard : K.edgeSet.ncard + 1 = 2 * n)
    {x p q : V} (hxs : x ∈ s) (hdeg : K.degree x = 3) (hxp : K.Adj x p) (hxq : K.Adj x q)
    (hpq : p ≠ q) (hnadj : ¬ K.Adj p q) (hn5 : 5 ≤ n) : False := by
  classical
  have hHcard : (K.deleteIncidenceSet x).edgeSet.ncard + 3 = K.edgeSet.ncard := by
    rw [← hdeg]; exact ncard_edgeSet_deleteIncidenceSet K x
  have hpH : s(p, q) ∉ (K.deleteIncidenceSet x).edgeSet := fun h ↦
    hnadj (deleteIncidenceSet_le K x h)
  have hGcard : ((K.deleteIncidenceSet x) ⊔ SimpleGraph.edge p q).edgeSet.ncard =
      (K.deleteIncidenceSet x).edgeSet.ncard + 1 := by
    rw [edgeSet_sup, edgeSet_edge_of_ne hpq, Set.union_singleton,
      Set.ncard_insert_of_notMem hpH (Set.toFinite _)]
  have hps : p ∈ s := hs p x hxp.symm
  have hqs : q ∈ s := hs q x hxq.symm
  have hG's : ∀ u v : V, ((K.deleteIncidenceSet x) ⊔ SimpleGraph.edge p q).Adj u v →
      u ∈ s.erase x := by
    intro u v huv
    rcases huv with huv | huv
    · obtain ⟨hadj, hux, -⟩ := deleteIncidenceSet_adj.mp huv
      exact Finset.mem_erase.mpr ⟨hux, hs u v hadj⟩
    · rcases (edge_adj ..).mp huv with ⟨h | h, -⟩
      · rw [h.1]; exact Finset.mem_erase.mpr ⟨hxp.ne', hps⟩
      · rw [h.1]; exact Finset.mem_erase.mpr ⟨hxq.ne', hqs⟩
  have hG'rail : ¬ HasVertexRails ((K.deleteIncidenceSet x) ⊔ SimpleGraph.edge p q) 4 :=
    fun hr ↦ hrail (hasVertexRails_of_sup_edge hxp hxq hpq (by norm_num) hr)
  have hecard : (s.erase x).card = n - 1 := by rw [Finset.card_erase_of_mem hxs, hcard]
  have hbound := ih (s.erase x) _ (by omega) ⟨p, Finset.mem_erase.mpr ⟨hxp.ne', hps⟩⟩
    hG's hG'rail
  omega

/-- Deleting the third vertex of a triangle of neighbours of `x` must separate the other two. -/
theorem not_reachable_of_triangle {V : Type*} [DecidableEq V] {K H₀ : SimpleGraph V} {x : V}
    {t : Set V}
    (hH₀ : ∀ u v : V, H₀.Adj u v ↔ (K.Adj u v ∧ u ≠ x ∧ v ≠ x ∧ ¬(u ∈ t ∧ v ∈ t)))
    {u v w : V} (hut : u ∈ t) (hvt : v ∈ t) (hxu : K.Adj x u) (hxv : K.Adj x v)
    (hxw : K.Adj x w) (huv : K.Adj u v) (huw : K.Adj u w) (hvw : K.Adj v w)
    (hrail : ¬ HasVertexRails K 4) : ¬ (H₀.deleteIncidenceSet w).Reachable u v := by
  intro hreach
  refine hrail (hasVertexRails_four_of_detour hxu hxv hxw huv huw hvw ?_ ?_ ?_ ?_ hreach)
  · intro z y h
    exact ((hH₀ z y).mp (deleteIncidenceSet_le _ _ h)).1
  · exact fun z hz ↦ ((hH₀ x z).mp (deleteIncidenceSet_le _ _ hz)).2.1 rfl
  · exact fun z hz ↦ (deleteIncidenceSet_adj.mp hz).2.1 rfl
  · exact fun hz ↦ ((hH₀ u v).mp (deleteIncidenceSet_le _ _ hz)).2.2.2 ⟨hut, hvt⟩

/-- Every `K`-edge leaving the `H₀`-component of `p` at a vertex other than `p` stays inside. -/
theorem reachable_of_adj_of_component {V : Type*} {K H₀ : SimpleGraph V} {x : V} {t : Set V}
    (hH₀ : ∀ u v : V,
      H₀.Adj u v ↔ (K.Adj u v ∧ u ≠ x ∧ v ≠ x ∧ ¬(u ∈ t ∧ v ∈ t)))
    {p : V} (hpt : p ∈ t) (hxt : x ∉ t) (hnb : ∀ z : V, K.Adj x z → z ∈ t)
    (hun : ∀ z ∈ t, z ≠ p → ¬ H₀.Reachable p z) {u v : V} (huv : K.Adj u v)
    (hu : H₀.Reachable p u) (hup : u ≠ p) : H₀.Reachable p v := by
  have hiso : ∀ y : V, ¬ H₀.Adj x y := fun y hy ↦ ((hH₀ x y).mp hy).2.1 rfl
  have hux : u ≠ x := by
    rintro rfl
    exact not_reachable_of_isolated hiso (fun h ↦ hxt (h ▸ hpt)) hu
  have hut : u ∉ t := fun h ↦ hun u h hup hu
  have hvx : v ≠ x := fun h ↦ hut (hnb u (h ▸ huv).symm)
  exact hu.trans (Adj.reachable ((hH₀ u v).mpr ⟨huv, hux, hvx, fun hc ↦ hut hc.1⟩))

/-- The case of a degree-three vertex whose three neighbours form a triangle. -/
theorem false_of_triangle {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (ih : RailBoundBelow V n) {s : Finset V} {K : SimpleGraph V}
    (hs : ∀ u v : V, K.Adj u v → u ∈ s) (hcard : s.card = n) (hrail : ¬ HasVertexRails K 4)
    (hKcard : K.edgeSet.ncard + 1 = 2 * n) (hn5 : 5 ≤ n) {x a b c : V} (hxs : x ∈ s)
    (hnbr : ∀ z : V, K.Adj x z → z = a ∨ z = b ∨ z = c) (hxa : K.Adj x a) (hxb : K.Adj x b)
    (hxc : K.Adj x c) (hab : K.Adj a b) (hac : K.Adj a c) (hbc : K.Adj b c) : False := by
  classical
  obtain ⟨t, htdef⟩ : ∃ t : Set V, t = {a, b, c} := ⟨_, rfl⟩
  obtain ⟨H₀, hH₀⟩ : ∃ H : SimpleGraph V, ∀ u v : V,
      H.Adj u v ↔ (K.Adj u v ∧ u ≠ x ∧ v ≠ x ∧ ¬(u ∈ t ∧ v ∈ t)) :=
      by
    refine ⟨(K.deleteIncidenceSet x).deleteEdges {e : Sym2 V | ∀ y ∈ e, y ∈ t},
      fun u v ↦ ?_⟩
    rw [deleteEdges_adj, deleteIncidenceSet_adj]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨h1, h2, h3, fun hc ↦ h4 fun y hy ↦ ?_⟩
      rcases Sym2.mem_iff.mp hy with rfl | rfl
      exacts [hc.1, hc.2]
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, h3⟩, fun hc ↦ h4 ⟨hc u (by simp), hc v (by simp)⟩⟩
  have hat : a ∈ t := by rw [htdef]; simp
  have hbt : b ∈ t := by rw [htdef]; simp
  have hct : c ∈ t := by rw [htdef]; simp
  have hmemt : ∀ z : V, z ∈ t → z = a ∨ z = b ∨ z = c := by
    intro z hz; rw [htdef] at hz; simpa using hz
  have hxt : x ∉ t := fun h ↦ by
    rcases hmemt x h with rfl | rfl | rfl
    exacts [hxa.ne rfl, hxb.ne rfl, hxc.ne rfl]
  have hnb' : ∀ z : V, K.Adj x z → z ∈ t := by
    intro z hz
    rcases hnbr z hz with rfl | rfl | rfl
    exacts [hat, hbt, hct]
  have has : a ∈ s := hs a x hxa.symm
  have hbs : b ∈ s := hs b x hxb.symm
  have hcs : c ∈ s := hs c x hxc.symm
  have hH₀K : ∀ u v : V, H₀.Adj u v → K.Adj u v := fun u v h ↦ ((hH₀ u v).mp h).1
  have r1 : ¬ (H₀.deleteIncidenceSet c).Reachable a b :=
    not_reachable_of_triangle hH₀ hat hbt hxa hxb hxc hab hac hbc hrail
  have r2 : ¬ (H₀.deleteIncidenceSet b).Reachable a c :=
    not_reachable_of_triangle hH₀ hat hct hxa hxc hxb hac hab hbc.symm hrail
  have r3 : ¬ (H₀.deleteIncidenceSet a).Reachable b c :=
    not_reachable_of_triangle hH₀ hbt hct hxb hxc hxa hbc hab.symm hac.symm hrail
  have r4 : ¬ (H₀.deleteIncidenceSet a).Reachable c b :=
    not_reachable_of_triangle hH₀ hct hbt hxc hxb hxa hbc.symm hac.symm hab.symm hrail
  have nab : ¬ H₀.Reachable a b := not_reachable_of_pair hac.ne r1 r4
  have nac : ¬ H₀.Reachable a c := not_reachable_of_pair hab.ne r2 r3
  have nbc : ¬ H₀.Reachable b c := not_reachable_of_pair hab.ne' r3 r2
  have hcase : ∀ p q : V, p ∈ t → p ∈ s → q ∈ s →
      (∀ z ∈ t, z ≠ p → ¬ H₀.Reachable p z) → ¬ H₀.Reachable p q →
      (∃ z : V, H₀.Adj p z) → False := by
    rintro p q hpt hps hqs hun hpq ⟨z, hz⟩
    exact false_of_cut ih hs hcard hrail hKcard {y | H₀.Reachable p y} p
      (Reachable.refl p) hps
      (fun u v huv hu hup ↦ reachable_of_adj_of_component hH₀ hpt hxt hnb' hun huv hu hup)
      ⟨z, hs z p (hH₀K p z hz).symm, hz.reachable, hz.ne'⟩ ⟨q, hqs, hpq⟩
  by_cases hA : ∃ z : V, H₀.Adj a z
  · refine hcase a b hat has hbs (fun z hzt hza ↦ ?_) nab hA
    rcases hmemt z hzt with rfl | rfl | rfl
    exacts [absurd rfl hza, nab, nac]
  by_cases hB : ∃ z : V, H₀.Adj b z
  · refine hcase b a hbt hbs has (fun z hzt hzb ↦ ?_) (fun h ↦ nab h.symm) hB
    rcases hmemt z hzt with rfl | rfl | rfl
    exacts [fun h ↦ nab h.symm, absurd rfl hzb, nbc]
  by_cases hC : ∃ z : V, H₀.Adj c z
  · refine hcase c a hct hcs has (fun z hzt hzc ↦ ?_) (fun h ↦ nac h.symm) hC
    rcases hmemt z hzt with rfl | rfl | rfl
    exacts [fun h ↦ nac h.symm, fun h ↦ nbc h.symm, absurd rfl hzc]
  push Not at hA hB hC
  have hiso : ∀ z : V, z ∈ t → ∀ y : V, ¬ H₀.Adj z y := by
    intro z hz y
    rcases hmemt z hz with rfl | rfl | rfl
    exacts [hA y, hB y, hC y]
  refine false_of_cut ih hs hcard hrail hKcard (insert x t) x (Set.mem_insert _ _) hxs ?_
    ⟨a, has, Set.mem_insert_of_mem _ hat, hxa.ne'⟩ ?_
  · intro u v huv hu hux
    have hut : u ∈ t := by
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact absurd rfl hux
      · exact hu
    have hnH : ¬ H₀.Adj u v := hiso u hut v
    rw [hH₀ u v] at hnH
    push Not at hnH
    rcases eq_or_ne v x with rfl | hvx
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hnH huv hux hvx).2
  · by_contra hcon
    push Not at hcon
    have hsub : s ⊆ ({x, a, b, c} : Finset V) := by
      intro z hz
      rcases Set.mem_insert_iff.mp (hcon z hz) with rfl | hz'
      · simp
      · rcases hmemt z hz' with rfl | rfl | rfl <;> simp
    have hle := Finset.card_le_card hsub
    have h4 : (({x, a, b, c} : Finset V)).card ≤ 4 := by
      refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    omega

/-- **Bollobás' bound.**  A graph with no `4`-rail whose edges lie inside a nonempty set `s` of
`n` vertices has at most `2n − 2` edges. -/
theorem card_edgeSet_add_two_le {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) :
    ∀ (s : Finset V) (G : SimpleGraph V), s.card = n → s.Nonempty →
      (∀ u v : V, G.Adj u v → u ∈ s) → ¬ HasVertexRails G 4 →
      G.edgeSet.ncard + 2 ≤ 2 * n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro s G hn hne hs hrail
  classical
  have ih : RailBoundBelow V n := fun u Kg hlt hnu hsu hru ↦ IH u.card hlt u Kg rfl hnu hsu hru
  by_contra hcon
  push Not at hcon
  have hn1 : 1 ≤ n := by rw [← hn]; exact Finset.card_pos.mpr hne
  have hchoose : 2 * G.edgeSet.ncard ≤ n * (n - 1) := by
    have h := two_mul_ncard_edgeSet_le (s := s) (G := G) hs
    rwa [hn] at h
  have hn5 : 5 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n <;> omega
  obtain ⟨K, hKle, hKcard0⟩ := exists_le_ncard_edgeSet_eq G (k := 2 * n - 1) (by omega)
  have hKcard : K.edgeSet.ncard + 1 = 2 * n := by omega
  have hKs : ∀ u v : V, K.Adj u v → u ∈ s := fun u v huv ↦ hs u v (hKle huv)
  have hKrail : ¬ HasVertexRails K 4 := fun hr ↦ hrail (hasVertexRails_mono hKle hr)
  have hdeg3 : ∃ x ∈ s, K.degree x ≤ 3 := by
    by_contra hall
    push Not at hall
    have hsum := sum_degree_eq_two_mul (s := s) (G := K) hKs
    have hge : 4 * n ≤ ∑ w ∈ s, K.degree w := by
      calc 4 * n = ∑ _w ∈ s, 4 := by rw [Finset.sum_const, smul_eq_mul, hn, mul_comm]
        _ ≤ ∑ w ∈ s, K.degree w := Finset.sum_le_sum fun w hw ↦ hall w hw
    omega
  obtain ⟨x, hxs, hxdeg⟩ := hdeg3
  have hHcard : (K.deleteIncidenceSet x).edgeSet.ncard + K.degree x = K.edgeSet.ncard :=
    ncard_edgeSet_deleteIncidenceSet K x
  have hHs : ∀ u v : V, (K.deleteIncidenceSet x).Adj u v → u ∈ s.erase x := by
    intro u v huv
    obtain ⟨hadj, hux, -⟩ := deleteIncidenceSet_adj.mp huv
    exact Finset.mem_erase.mpr ⟨hux, hKs u v hadj⟩
  have hHrail : ¬ HasVertexRails (K.deleteIncidenceSet x) 4 :=
    fun hr ↦ hKrail (hasVertexRails_mono (deleteIncidenceSet_le K x) hr)
  have hecard : (s.erase x).card = n - 1 := by rw [Finset.card_erase_of_mem hxs, hn]
  have hene : (s.erase x).Nonempty := Finset.card_pos.mp (by omega)
  have hHbound := ih (s.erase x) _ (by omega) hene hHs hHrail
  rcases Nat.lt_or_ge (K.degree x) 3 with hlt3 | hge3
  · omega
  have hdeg : K.degree x = 3 := le_antisymm hxdeg hge3
  have hnbcard : (K.neighborFinset x).card = 3 := by rw [card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, c, hab', hac', hbc', hnb⟩ := Finset.card_eq_three.mp hnbcard
  have hmemnb : ∀ z : V, K.Adj x z ↔ z = a ∨ z = b ∨ z = c := by
    intro z
    rw [← mem_neighborFinset, hnb]
    simp
  have hxa : K.Adj x a := (hmemnb a).mpr (Or.inl rfl)
  have hxb : K.Adj x b := (hmemnb b).mpr (Or.inr (Or.inl rfl))
  have hxc : K.Adj x c := (hmemnb c).mpr (Or.inr (Or.inr rfl))
  by_cases hABn : K.Adj a b
  case neg => exact false_of_nonadj ih hKs hn hKrail hKcard hxs hdeg hxa hxb hab' hABn hn5
  by_cases hACn : K.Adj a c
  case neg => exact false_of_nonadj ih hKs hn hKrail hKcard hxs hdeg hxa hxc hac' hACn hn5
  by_cases hBCn : K.Adj b c
  case neg => exact false_of_nonadj ih hKs hn hKrail hKcard hxs hdeg hxb hxc hbc' hBCn hn5
  exact false_of_triangle ih hKs hn hKrail hKcard hn5 hxs (fun z hz ↦ (hmemnb z).mp hz)
    hxa hxb hxc hABn hACn hBCn

end Induction

section Main

/-- **Bollobás 1966.**  A graph on `N ≥ 4` vertices with at least `2N − 1` edges has two
vertices joined by four internally disjoint paths. -/
theorem hasVertexRails_four_of_edges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : 4 ≤ Fintype.card V) (h : 2 * Fintype.card V - 1 ≤ G.edgeSet.ncard) :
    HasVertexRails G 4 := by
  classical
  by_contra hrail
  have hne : (Finset.univ : Finset V).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  have hcard : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hb := card_edgeSet_add_two_le (V := V) (Fintype.card V) Finset.univ G hcard hne
    (fun u v _ ↦ Finset.mem_univ u) hrail
  omega

/-- The Bollobás–Erdős conjecture for `m = 4`, vertex-disjoint reading. -/
theorem vertex_rails_four {n : ℕ} (hn : 1 ≤ n) {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 1 + n * (4 - 1)) (hE : G.edgeSet.ncard = 1 + n * Nat.choose 4 2) :
    HasVertexRails G 4 := by
  have hc : Nat.choose 4 2 = 6 := by decide
  rw [hc] at hE
  exact hasVertexRails_four_of_edges G (by omega) (by omega)

end Main


end Erdos915
