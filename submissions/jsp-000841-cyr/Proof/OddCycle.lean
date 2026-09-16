import Proof.Defs

/-!
# Erdős Problem 1011: a graph that is not `2`-colourable contains an odd cycle

If every closed walk of `G` has even length, colouring each vertex by the parity of its distance to
a fixed representative of its connected component is a proper `2`-colouring.  Hence a graph that is
not `2`-colourable has a closed walk of odd length; a closed walk of minimal odd length is a cycle
(a repeated vertex would split it into two shorter closed walks, one of them odd).
-/

open SimpleGraph

namespace Erdos1011

/-- A walk whose support repeats a vertex splits off a nontrivial closed walk. -/
private theorem exists_closed_walk_of_not_support_nodup {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬ p.support.Nodup) :
    ∃ (x : V) (c : G.Walk x x) (q : G.Walk u v), 0 < c.length ∧
      c.length + q.length = p.length := by
  induction p with
  | nil => simp at hp
  | cons hab t ih =>
    rename_i a b _
    simp only [Walk.support_cons, List.nodup_cons, not_and_or, not_not] at hp
    rcases hp with ha | ht
    · refine ⟨a, Walk.cons hab (t.takeUntil a ha), t.dropUntil a ha, by simp, ?_⟩
      have hsplit := congrArg Walk.length (t.take_spec ha)
      rw [Walk.length_append] at hsplit
      simp only [Walk.length_cons]
      omega
    · obtain ⟨x, c, q, hc, hlen⟩ := ih ht
      refine ⟨x, c, Walk.cons hab q, hc, ?_⟩
      simp only [Walk.length_cons]
      omega

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- A graph all of whose closed walks have even length is `2`-colourable. -/
theorem colorable_two_of_forall_even (G : SimpleGraph V)
    (h : ∀ (v : V) (p : G.Walk v v), Even p.length) : G.Colorable 2 := by
  classical
  have hreach : ∀ x : V, G.Reachable (Quot.out (G.connectedComponentMk x)) x := fun x ↦
    ConnectedComponent.exact (Quot.out_eq (G.connectedComponentMk x))
  refine ⟨Coloring.mk
    (fun x ↦ if Even (G.dist (Quot.out (G.connectedComponentMk x)) x) then (0 : Fin 2) else 1)
    fun {x y} hxy ↦ ?_⟩
  have hout : Quot.out (G.connectedComponentMk x) = Quot.out (G.connectedComponentMk y) :=
    congrArg Quot.out (ConnectedComponent.sound hxy.reachable)
  have hry : G.Reachable (Quot.out (G.connectedComponentMk x)) y := by
    rw [hout]; exact hreach y
  obtain ⟨px, hpx⟩ := (hreach x).exists_walk_length_eq_dist
  obtain ⟨py, hpy⟩ := hry.exists_walk_length_eq_dist
  have hlen : Even (px.append (Walk.cons hxy py.reverse)).length := h _ _
  rw [Walk.length_append, Walk.length_cons, Walk.length_reverse, hpx, hpy] at hlen
  rw [← hout]
  by_cases hx : Even (G.dist (Quot.out (G.connectedComponentMk x)) x)
  · have hy : ¬ Even (G.dist (Quot.out (G.connectedComponentMk x)) y) := by
      simp only [Nat.even_iff] at hlen hx ⊢
      omega
    simp [hx, hy]
  · have hy : Even (G.dist (Quot.out (G.connectedComponentMk x)) y) := by
      simp only [Nat.even_iff] at hlen hx ⊢
      omega
    simp [hx, hy]

omit [Fintype V] in
/-- A closed walk of minimal odd length is a cycle. -/
theorem isCycle_of_minimal_odd (G : SimpleGraph V) {v : V} (p : G.Walk v v) (hp : Odd p.length)
    (hmin : ∀ (w : V) (q : G.Walk w w), Odd q.length → p.length ≤ q.length) : p.IsCycle := by
  obtain ⟨w, hvw, p', rfl⟩ :
      ∃ (w : V) (h : G.Adj v w) (q : G.Walk w v), p = Walk.cons h q := by
    refine Walk.not_nil_iff.mp fun hnil ↦ ?_
    rw [Nat.odd_iff, hnil.length_eq_zero] at hp
    exact absurd hp (by decide)
  have hpodd : (Walk.cons hvw p').length % 2 = 1 := Nat.odd_iff.mp hp
  have hpath : p'.IsPath := by
    rw [Walk.isPath_def]
    by_contra hnd
    obtain ⟨x, c, q, hc, hlen⟩ := exists_closed_walk_of_not_support_nodup p' hnd
    have hq : 0 < (Walk.cons hvw q).length := by simp
    have hsum : c.length + (Walk.cons hvw q).length = (Walk.cons hvw p').length := by
      simp only [Walk.length_cons]
      omega
    rcases Nat.even_or_odd c.length with hce | hco
    · have hodd : Odd (Walk.cons hvw q).length := by
        rw [Nat.odd_iff]
        rw [Nat.even_iff] at hce
        omega
      have hle := hmin v (Walk.cons hvw q) hodd
      omega
    · have hle := hmin x c hco
      omega
  have hlen2 : 2 ≤ p'.length := by
    have h0 : p'.length ≠ 0 := by
      intro h0
      have hwv : w = v := Walk.eq_of_length_eq_zero h0
      subst hwv
      exact G.ne_of_adj hvw rfl
    simp only [Walk.length_cons] at hpodd
    omega
  have hedge : s(v, w) ∉ p'.edges := by
    intro he
    have hrev : p'.reverse.IsPath := hpath.reverse
    obtain ⟨z, hvz, t, ht⟩ : ∃ (z : V) (h : G.Adj v z) (q : G.Walk z w),
        p'.reverse = Walk.cons h q := by
      refine Walk.not_nil_iff.mp ?_
      rw [Walk.not_nil_iff_lt_length, Walk.length_reverse]
      omega
    rw [ht, Walk.cons_isPath_iff] at hrev
    have he' : s(v, w) ∈ p'.reverse.edges := by
      rw [Walk.edges_reverse]
      exact List.mem_reverse.mpr he
    rw [ht, Walk.edges_cons, List.mem_cons] at he'
    rcases he' with heq | hmem
    · have hzw : z = w := by
        rcases Sym2.eq_iff.mp heq with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2.symm
        · exact absurd h2.symm (G.ne_of_adj hvw)
      subst hzw
      have htnil : t.Nil := Walk.isPath_iff_nil.mp hrev.1
      have h1 : p'.reverse.length = 1 := by
        rw [ht, Walk.length_cons, htnil.length_eq_zero]
      rw [Walk.length_reverse] at h1
      omega
    · exact absurd (Walk.fst_mem_support_of_mem_edges _ hmem) hrev.2
  exact (Walk.cons_isCycle_iff p' hvw).mpr ⟨hpath, hedge⟩

/-- A graph that is not `2`-colourable contains an odd cycle. -/
theorem exists_odd_cycle (G : SimpleGraph V) (h : ¬ G.Colorable 2) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length := by
  classical
  by_cases hall : ∀ (v : V) (p : G.Walk v v), Even p.length
  · exact absurd (colorable_two_of_forall_even G hall) h
  simp only [not_forall, Nat.not_even_iff_odd] at hall
  obtain ⟨v, p, hodd⟩ := hall
  have hne : Set.Nonempty {m : ℕ | ∃ (u : V) (r : G.Walk u u), Odd r.length ∧ r.length = m} :=
    ⟨p.length, v, p, hodd, rfl⟩
  obtain ⟨w, q, hqodd, hqlen⟩ := Nat.sInf_mem hne
  refine ⟨w, q, isCycle_of_minimal_odd G q hqodd ?_, hqodd⟩
  intro u r hr
  rw [hqlen]
  exact Nat.sInf_le ⟨u, r, hr, rfl⟩

end Erdos1011
