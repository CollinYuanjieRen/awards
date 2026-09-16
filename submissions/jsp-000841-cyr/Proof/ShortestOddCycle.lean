import Proof.Defs

/-!
# Erdős Problem 1011: structure of a shortest odd cycle in a triangle-free graph

Let `c` be an odd cycle of minimal length among all odd cycles of `G`, and let `G` be
triangle-free.  Then `c` has length at least `5`, `c` is chordless (every edge of `G` between two
vertices of `c` is an edge of `c`), and every vertex outside `c` has at most two neighbours on `c`
(two neighbours of an outside vertex `v` on `c` cut `c` into two arcs; the arc together with the two
edges at `v` of the wrong parity is an odd cycle, which must be at least as long as `c`, so the other
arc has length `2`; three neighbours would then force pairwise arc-distances `2`, impossible on an
odd cycle).
-/

open Finset SimpleGraph

namespace Erdos1011

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The vertex set of a walk. -/
def vset {u v : V} (p : G.Walk u v) : Finset V := p.support.toFinset

/-- `c` is an odd cycle of minimal length among the odd cycles of `G`. -/
def IsShortestOddCycle {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ Odd c.length ∧
    ∀ (w : V) (c' : G.Walk w w), c'.IsCycle → Odd c'.length → c.length ≤ c'.length

omit [DecidableEq V] in
/-- If `G` has an odd cycle, it has a shortest one. -/
theorem exists_isShortestOddCycle (h : ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length) :
    ∃ (v : V) (c : G.Walk v v), IsShortestOddCycle c := by
  classical
  obtain ⟨v, c, hcyc, hodd⟩ := h
  have hex : ∃ n : ℕ, ∃ (w : V) (c' : G.Walk w w), c'.IsCycle ∧ Odd c'.length ∧ c'.length = n :=
    ⟨c.length, v, c, hcyc, hodd, rfl⟩
  obtain ⟨w, c', hcyc', hodd', hlen⟩ := Nat.find_spec hex
  refine ⟨w, c', hcyc', hodd', fun u e he hoe ↦ ?_⟩
  rw [hlen]
  exact Nat.find_min' hex ⟨u, e, he, hoe, rfl⟩

omit [Fintype V] in
/-- A cycle visits `length` distinct vertices. -/
theorem card_vset_eq_length {v : V} {c : G.Walk v v} (hc : c.IsCycle) : (vset c).card = c.length := by
  have hv : v ∈ c.support.tail := Walk.end_mem_tail_support hc.not_nil
  have h1 : c.support.toFinset = c.support.tail.toFinset := by
    conv_lhs => rw [← Walk.cons_tail_support c]
    rw [List.toFinset_cons, Finset.insert_eq_self]
    exact List.mem_toFinset.mpr hv
  have h2 : c.support.tail.length = c.length := by
    rw [List.length_tail, Walk.length_support]
    omega
  simp only [vset]
  rw [h1, List.toFinset_card_of_nodup hc.support_nodup, h2]

omit [Fintype V] in
/-- An odd cycle in a triangle-free graph has length at least `5`. -/
theorem five_le_length (hG : G.CliqueFree 3) {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    (ho : Odd c.length) : 5 ≤ c.length := by
  have h3 : 3 ≤ c.length := hc.three_le_length
  have hodd : c.length % 2 = 1 := Nat.odd_iff.mp ho
  by_contra hlt
  have hl : c.length = 3 := by omega
  have h01 : G.Adj (c.getVert 0) (c.getVert 1) := c.adj_getVert_succ (by omega)
  have h12 : G.Adj (c.getVert 1) (c.getVert 2) := c.adj_getVert_succ (by omega)
  have h23 : G.Adj (c.getVert 2) (c.getVert 3) := c.adj_getVert_succ (by omega)
  have e3 : c.getVert 3 = v := by rw [← hl]; exact c.getVert_length
  have e0 : c.getVert 0 = v := c.getVert_zero
  have e30 : c.getVert 3 = c.getVert 0 := by rw [e3, e0]
  rw [e30] at h23
  exact hG {c.getVert 0, c.getVert 1, c.getVert 2}
    (is3Clique_triple_iff.mpr ⟨h01, h23.symm, h12⟩)

omit [Fintype V] in
/-- Two distinct neighbours of a vertex off a shortest odd cycle cut the cycle into two arcs, one
of which has length exactly `2`. -/
private lemma arc_length_eq_two (hG : G.CliqueFree 3) {v : V} {c : G.Walk v v}
    (hc : IsShortestOddCycle c) {x y z : V} (hx : x ∉ c.support) (hyz : y ≠ z)
    (hxy : G.Adj x y) (hxz : G.Adj x z) {p₁ : G.Walk y z} {p₂ : G.Walk z y}
    (h₁ : p₁.IsPath) (h₂ : p₂.IsPath) (hs₁ : ∀ w ∈ p₁.support, w ∈ c.support)
    (hs₂ : ∀ w ∈ p₂.support, w ∈ c.support) (hlen : p₁.length + p₂.length = c.length) :
    p₁.length = 2 ∨ p₂.length = 2 := by
  obtain ⟨-, hodd, hmin⟩ := hc
  have hx₁ : x ∉ p₁.support := fun hw ↦ hx (hs₁ x hw)
  have hx₂ : x ∉ p₂.support := fun hw ↦ hx (hs₂ x hw)
  have he₁ : (Walk.cons hxy (p₁.concat hxz.symm)).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨h₁.concat hx₁ hxz.symm, ?_⟩
    rw [Walk.edges_concat, List.concat_eq_append]
    simp only [List.mem_append, List.mem_singleton, not_or]
    refine ⟨fun hw ↦ hx₁ (p₁.fst_mem_support_of_mem_edges hw), fun hw ↦ ?_⟩
    rw [Sym2.eq_iff] at hw
    rcases hw with ⟨-, h⟩ | ⟨-, h⟩
    · exact hxy.ne h.symm
    · exact hyz h
  have he₂ : (Walk.cons hxz (p₂.concat hxy.symm)).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨h₂.concat hx₂ hxy.symm, ?_⟩
    rw [Walk.edges_concat, List.concat_eq_append]
    simp only [List.mem_append, List.mem_singleton, not_or]
    refine ⟨fun hw ↦ hx₂ (p₂.fst_mem_support_of_mem_edges hw), fun hw ↦ ?_⟩
    rw [Sym2.eq_iff] at hw
    rcases hw with ⟨-, h⟩ | ⟨-, h⟩
    · exact hxz.ne h.symm
    · exact hyz h.symm
  have hl₁ : (Walk.cons hxy (p₁.concat hxz.symm)).length = p₁.length + 2 := by
    rw [Walk.length_cons, Walk.length_concat]
  have hl₂ : (Walk.cons hxz (p₂.concat hxy.symm)).length = p₂.length + 2 := by
    rw [Walk.length_cons, Walk.length_concat]
  have hz₁ : p₁.length ≠ 0 := fun h ↦ hyz (Walk.eq_of_length_eq_zero h)
  have hz₂ : p₂.length ≠ 0 := fun h ↦ hyz (Walk.eq_of_length_eq_zero h).symm
  have hadj : ∀ {s t : V} (q : G.Walk s t), q.length = 1 → G.Adj s t := by
    intro s t q hq
    have h0 : q.getVert 0 = s := q.getVert_zero
    have h1 : q.getVert 1 = t := by rw [← hq]; exact q.getVert_length
    have := q.adj_getVert_succ (i := 0) (by omega)
    rwa [h0, h1] at this
  have ho₁ : p₁.length ≠ 1 := fun h ↦
    hG {x, y, z} (is3Clique_triple_iff.mpr ⟨hxy, hxz, hadj p₁ h⟩)
  have ho₂ : p₂.length ≠ 1 := fun h ↦
    hG {x, y, z} (is3Clique_triple_iff.mpr ⟨hxy, hxz, (hadj p₂ h).symm⟩)
  have hoddc : c.length % 2 = 1 := Nat.odd_iff.mp hodd
  by_cases hpar : p₁.length % 2 = 1
  · have hle := hmin x _ he₁ (Nat.odd_iff.mpr (by rw [hl₁]; omega))
    rw [hl₁] at hle
    right; omega
  · have hle := hmin x _ he₂ (Nat.odd_iff.mpr (by rw [hl₂]; omega))
    rw [hl₂] at hle
    left; omega

omit [Fintype V] in
/-- In a cycle, a vertex other than the base point occurs at a single index, so `takeUntil`
records that index. -/
private lemma length_takeUntil_eq_of_getVert {u y : V} {k : G.Walk u u} (hk : k.IsCycle)
    (hy : y ∈ k.support) (hyu : y ≠ u) {n : ℕ} (hn : n ≤ k.length) (hgv : k.getVert n = y) :
    (k.takeUntil y hy).length = n := by
  have h0 : k.getVert (k.takeUntil y hy).length = y := k.getVert_length_takeUntil hy
  have h1 : (k.takeUntil y hy).length ≤ k.length := k.length_takeUntil_le_length hy
  have h2 : 1 ≤ (k.takeUntil y hy).length := by
    rcases Nat.eq_zero_or_pos (k.takeUntil y hy).length with h | h
    · rw [h, k.getVert_zero] at h0
      exact absurd h0.symm hyu
    · exact h
  have h3 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, k.getVert_zero] at hgv
      exact absurd hgv.symm hyu
    · exact h
  exact hk.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) (h0.trans hgv.symm)

omit [Fintype V] in
/-- For a rotation `k` of a shortest odd cycle `c` based at a neighbour `y` of an outside vertex
`x`, any other neighbour `z` of `x` on `c` sits at index `2` or `c.length - 2` along `k`. -/
private lemma length_takeUntil_eq_two_or (hG : G.CliqueFree 3) {v : V} {c : G.Walk v v}
    (hc : IsShortestOddCycle c) {x y z : V} (hx : x ∉ c.support) (hxy : G.Adj x y)
    (hxz : G.Adj x z) (hyz : y ≠ z) {k : G.Walk y y} (hk : k.IsCycle) (hklen : k.length = c.length)
    (hksup : ∀ w ∈ k.support, w ∈ c.support) (hz : z ∈ k.support) :
    (k.takeUntil z hz).length = 2 ∨ (k.takeUntil z hz).length = c.length - 2 := by
  have h1 : (k.takeUntil z hz).IsPath := hk.isPath_takeUntil hz
  have hnil : ¬ (k.takeUntil z hz).Nil := by simp [hyz]
  have hcs : ((k.takeUntil z hz).append (k.dropUntil z hz)).IsCycle := by
    rw [k.take_spec hz]; exact hk
  have h2 : (k.dropUntil z hz).IsPath := hcs.isPath_of_append_right hnil
  have hsum : (k.takeUntil z hz).length + (k.dropUntil z hz).length = c.length := by
    rw [← Walk.length_append, k.take_spec hz, hklen]
  have hs₁ : ∀ w ∈ (k.takeUntil z hz).support, w ∈ c.support :=
    fun w hw ↦ hksup w (k.support_takeUntil_subset_support hz hw)
  have hs₂ : ∀ w ∈ (k.dropUntil z hz).support, w ∈ c.support :=
    fun w hw ↦ hksup w (k.support_dropUntil_subset_support hz hw)
  rcases arc_length_eq_two hG hc hx hyz hxy hxz h1 h2 hs₁ hs₂ hsum with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

omit [Fintype V] in
/-- A shortest odd cycle is chordless: an edge of `G` between two of its vertices is one of its
edges. -/
theorem mem_edges_of_adj (hG : G.CliqueFree 3) {v : V} {c : G.Walk v v}
    (hc : IsShortestOddCycle c) {a b : V} (ha : a ∈ vset c) (hb : b ∈ vset c) (hab : G.Adj a b) :
    s(a, b) ∈ c.edges := by
  obtain ⟨hcyc, hodd, hmin⟩ := hc
  have h5 : 5 ≤ c.length := five_le_length hG hcyc hodd
  have ha' : a ∈ c.support := by simpa [vset] using ha
  have hb' : b ∈ c.support := by simpa [vset] using hb
  by_contra hne
  obtain ⟨k, hk, hklen, hkedges, hbk⟩ :
      ∃ k : G.Walk a a, k.IsCycle ∧ k.length = c.length ∧ (∀ e ∈ k.edges, e ∈ c.edges) ∧
        b ∈ k.support :=
    ⟨c.rotate a ha', hcyc.rotate ha', by simp, fun e he ↦ (c.rotate_edges a ha').mem_iff.mp he,
      (c.mem_support_rotate_iff a ha').mpr hb'⟩
  have hp₁ : (k.takeUntil b hbk).IsPath := hk.isPath_takeUntil hbk
  have hnil : ¬ (k.takeUntil b hbk).Nil := by simp [hab.ne]
  have hcs : ((k.takeUntil b hbk).append (k.dropUntil b hbk)).IsCycle := by
    rw [k.take_spec hbk]; exact hk
  have hp₂ : (k.dropUntil b hbk).IsPath := hcs.isPath_of_append_right hnil
  have hsum : (k.takeUntil b hbk).length + (k.dropUntil b hbk).length = c.length := by
    rw [← Walk.length_append, k.take_spec hbk, hklen]
  have hd₁ : (Walk.cons hab.symm (k.takeUntil b hbk)).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hp₁, fun hw ↦ hne ?_⟩
    rw [Sym2.eq_swap]
    exact hkedges _ (k.edges_takeUntil_subset_edges hbk hw)
  have hd₂ : (Walk.cons hab (k.dropUntil b hbk)).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    exact ⟨hp₂, fun hw ↦ hne (hkedges _ (k.edges_dropUntil_subset_edges hbk hw))⟩
  have h1 : 3 ≤ (Walk.cons hab.symm (k.takeUntil b hbk)).length := hd₁.three_le_length
  have h2 : 3 ≤ (Walk.cons hab (k.dropUntil b hbk)).length := hd₂.three_le_length
  rw [Walk.length_cons] at h1 h2
  have hoddc : c.length % 2 = 1 := Nat.odd_iff.mp hodd
  by_cases hpar : (k.takeUntil b hbk).length % 2 = 0
  · have hle := hmin b _ hd₁ (Nat.odd_iff.mpr (by rw [Walk.length_cons]; omega))
    rw [Walk.length_cons] at hle
    omega
  · have hle := hmin a _ hd₂ (Nat.odd_iff.mpr (by rw [Walk.length_cons]; omega))
    rw [Walk.length_cons] at hle
    omega

/-- The edges of `G` inside the vertex set of a shortest odd cycle are exactly its `length` edges. -/
theorem card_edges_within (hG : G.CliqueFree 3) [DecidableRel G.Adj] {v : V} {c : G.Walk v v}
    (hc : IsShortestOddCycle c) :
    (G.edgeFinset.filter fun e => ∀ x ∈ e, x ∈ vset c).card = c.length := by
  have hset : (G.edgeFinset.filter fun e ↦ ∀ x ∈ e, x ∈ vset c) = c.edges.toFinset := by
    ext e
    induction e using Sym2.ind with
    | _ p q =>
      simp only [Finset.mem_filter, mem_edgeFinset, mem_edgeSet, List.mem_toFinset, Sym2.mem_iff,
        vset, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨hadj, hp, hq⟩
        exact mem_edges_of_adj hG hc (List.mem_toFinset.mpr hp) (List.mem_toFinset.mpr hq) hadj
      · intro he
        exact ⟨c.edges_subset_edgeSet he, c.fst_mem_support_of_mem_edges he,
          c.snd_mem_support_of_mem_edges he⟩
  rw [hset, List.toFinset_card_of_nodup hc.1.edges_nodup, Walk.length_edges]

/-- A vertex outside a shortest odd cycle of a triangle-free graph has at most two neighbours on
it. -/
theorem card_neighbors_le_two (hG : G.CliqueFree 3) [DecidableRel G.Adj] {v : V} {c : G.Walk v v}
    (hc : IsShortestOddCycle c) {x : V} (hx : x ∉ vset c) :
    (G.neighborFinset x ∩ vset c).card ≤ 2 := by
  by_contra hcard
  rw [Nat.not_le] at hcard
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp hcard
  simp only [Finset.mem_inter, mem_neighborFinset, vset, List.mem_toFinset] at ha hb hd
  obtain ⟨hxa, haS⟩ := ha
  obtain ⟨hxb, hbS⟩ := hb
  obtain ⟨hxd, hdS⟩ := hd
  have hx' : x ∉ c.support := by simpa [vset] using hx
  have h5 : 5 ≤ c.length := five_le_length hG hc.1 hc.2.1
  have hoddc : c.length % 2 = 1 := Nat.odd_iff.mp hc.2.1
  obtain ⟨k, hk, hklen, hksup, hkmem⟩ :
      ∃ k : G.Walk a a, k.IsCycle ∧ k.length = c.length ∧
        (∀ w ∈ k.support, w ∈ c.support) ∧ ∀ w ∈ c.support, w ∈ k.support :=
    ⟨c.rotate a haS, hc.1.rotate haS, by simp,
      fun w hw ↦ (c.mem_support_rotate_iff a haS).mp hw,
      fun w hw ↦ (c.mem_support_rotate_iff a haS).mpr hw⟩
  have hbk : b ∈ k.support := hkmem b hbS
  have hdk : d ∈ k.support := hkmem d hdS
  have key : ∀ (y z : V), G.Adj x y → G.Adj x z → y ≠ z →
      ∀ (hyk : y ∈ k.support) (hzk : z ∈ k.support), (k.takeUntil y hyk).length = 2 →
        (k.takeUntil z hzk).length = c.length - 2 → False := by
    intro y z hxy hxz hyz hyk hzk hy2 hz2
    have hsum : (k.takeUntil z hzk).length + (k.dropUntil z hzk).length = c.length := by
      rw [← Walk.length_append, k.take_spec hzk, hklen]
    have hdrop : (k.dropUntil z hzk).length = 2 := by omega
    have hrlen : (k.rotate z hzk).length = c.length := by rw [Walk.length_rotate, hklen]
    have hye : y ∈ (k.rotate z hzk).support := (k.mem_support_rotate_iff z hzk).mpr hyk
    have hgv : (k.rotate z hzk).getVert 4 = y := by
      rw [Walk.rotate, Walk.getVert_append, hdrop]
      norm_num
      rw [Walk.getVert_takeUntil hzk (by omega), ← hy2]
      exact k.getVert_length_takeUntil hyk
    have h4 : ((k.rotate z hzk).takeUntil y hye).length = 4 :=
      length_takeUntil_eq_of_getVert (hk.rotate hzk) hye hyz (by omega) hgv
    rcases length_takeUntil_eq_two_or hG hc hx' hxz hxy hyz.symm (hk.rotate hzk) hrlen
      (fun w hw ↦ hksup w ((k.mem_support_rotate_iff z hzk).mp hw)) hye with h | h
    · omega
    · omega
  have hgb : k.getVert ((k.takeUntil b hbk).length) = b := k.getVert_length_takeUntil hbk
  have hgd : k.getVert ((k.takeUntil d hdk).length) = d := k.getVert_length_takeUntil hdk
  have hposne : (k.takeUntil b hbk).length ≠ (k.takeUntil d hdk).length :=
    fun h ↦ hbd (by rw [← hgb, h, hgd])
  have hib := length_takeUntil_eq_two_or hG hc hx' hxa hxb hab hk hklen hksup hbk
  have hid := length_takeUntil_eq_two_or hG hc hx' hxa hxd had hk hklen hksup hdk
  rcases hib with h₁ | h₁ <;> rcases hid with h₂ | h₂
  · exact hposne (h₁.trans h₂.symm)
  · exact key b d hxb hxd hbd hbk hdk h₁ h₂
  · exact key d b hxd hxb hbd.symm hdk hbk h₂ h₁
  · exact hposne (h₁.trans h₂.symm)

end Erdos1011
