import Proof.Ramsey

/-!
# Erdős problem #82 — regular induced subgraphs

Erdős, Fajtlowicz and Stanton asked how large a *regular induced subgraph* is guaranteed
in an arbitrary graph on `n` vertices.

This file sets up the two functions appearing on the problem page:

* `Erdos82.regGuarantee m` is `F(m)`, the largest `n` such that **every** graph on `m`
  vertices contains a regular induced subgraph on at least `n` vertices;
* `Erdos82.regThreshold n` is `G(n)`, the least `m` such that every graph on `m` vertices
  contains a regular induced subgraph on at least `n` vertices.

The basic bridge to Ramsey theory is `Erdos82.regProp_of_ramseyProp`: a monochromatic
`K_n` (in either colour) is a regular induced subgraph on `n` vertices.
-/

namespace Erdos82

open SimpleGraph

open Classical in
/-- `S` induces a regular subgraph of `G`: all vertices of `S` have the same number of
neighbours inside `S`. -/
noncomputable def IsRegularOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ d : ℕ, ∀ v ∈ S, (S.filter (fun w => G.Adj v w)).card = d

/-- `G` has a regular induced subgraph on at least `n` vertices. -/
def HasRegularInduced {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ S : Finset V, n ≤ S.card ∧ IsRegularOn G S

/-- Every graph on `m` vertices has a regular induced subgraph on at least `n` vertices. -/
def RegProp (m n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin m), HasRegularInduced G n

/-- `G(n)`: the least `m` such that every graph on `m` vertices contains a regular
induced subgraph on at least `n` vertices. -/
noncomputable def regThreshold (n : ℕ) : ℕ := sInf {m : ℕ | RegProp m n}

/-- `F(m)`: the largest `n` such that every graph on `m` vertices contains a regular
induced subgraph on at least `n` vertices. -/
noncomputable def regGuarantee (m : ℕ) : ℕ := sSup {n : ℕ | RegProp m n}

section Basic

variable {V : Type*} {G : SimpleGraph V}

/-- The empty set induces a regular subgraph (vacuously). -/
theorem isRegularOn_empty (G : SimpleGraph V) : IsRegularOn G (∅ : Finset V) :=
  ⟨0, by simp⟩

/-- Any pair of vertices induces a regular subgraph: either they are adjacent, and both
have one neighbour inside the pair, or they are not, and both have none. -/
theorem isRegularOn_pair [DecidableEq V] (G : SimpleGraph V) (a b : V) :
    IsRegularOn G ({a, b} : Finset V) := by
  classical
  have ha : ({a, b} : Finset V).filter (fun w => G.Adj a w)
      = if G.Adj a b then {b} else ∅ := by
    rw [Finset.filter_insert, Finset.filter_singleton]
    simp
  have hb : ({a, b} : Finset V).filter (fun w => G.Adj b w)
      = if G.Adj a b then {a} else ∅ := by
    rw [Finset.filter_insert, Finset.filter_singleton, G.adj_comm b a]
    simp
  refine ⟨if G.Adj a b then 1 else 0, ?_⟩
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · rw [ha]; split <;> simp
  · rw [hb]; split <;> simp

/-- A single vertex induces a regular subgraph. -/
theorem isRegularOn_singleton (G : SimpleGraph V) (a : V) :
    IsRegularOn G ({a} : Finset V) := by
  classical
  refine ⟨0, ?_⟩
  intro v hv
  simp only [Finset.mem_singleton] at hv
  subst hv
  rw [Finset.filter_singleton]
  simp

/-- A clique of `G` induces a regular subgraph: every vertex of a clique `S` has exactly
`S.card - 1` neighbours inside `S`. -/
theorem isRegularOn_of_isClique {S : Finset V} (h : G.IsClique (S : Set V)) :
    IsRegularOn G S := by
  classical
  refine ⟨S.card - 1, ?_⟩
  intro v hv
  have hfilter : S.filter (fun w => G.Adj v w) = S.erase v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun hw => ⟨fun hc => G.irrefl (hc ▸ hw.2), hw.1⟩
    · exact fun hw => ⟨hw.2, h hv hw.2 (Ne.symm hw.1)⟩
  rw [hfilter, Finset.card_erase_of_mem hv]

/-- A clique of the complement `Gᶜ` induces a regular subgraph of `G`, of degree `0`. -/
theorem isRegularOn_of_isClique_compl {S : Finset V} (h : Gᶜ.IsClique (S : Set V)) :
    IsRegularOn G S := by
  classical
  refine ⟨0, ?_⟩
  intro v hv
  have hfilter : S.filter (fun w => G.Adj v w) = ∅ := by
    ext w
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hw hadj
    have hne : v ≠ w := G.ne_of_adj hadj
    exact ((SimpleGraph.compl_adj _ _ _).mp (h hv hw hne)).2 hadj
  rw [hfilter, Finset.card_empty]

end Basic

/-- Ramsey's theorem feeds directly into the problem: a red `K_n` or a blue `K_n` is a
regular induced subgraph on `n` vertices. -/
theorem regProp_of_ramseyProp {m n : ℕ} (h : RamseyProp m n n) : RegProp m n := by
  intro G
  have hG := h G
  simp only [IsGood, not_and_or, SimpleGraph.CliqueFree, not_forall, not_not] at hG
  rcases hG with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨t, ht.2.ge, isRegularOn_of_isClique ht.1⟩
  · exact ⟨t, ht.2.ge, isRegularOn_of_isClique_compl ht.1⟩

/-- Every graph has a regular induced subgraph on at least `0` vertices. -/
theorem regProp_zero (m : ℕ) : RegProp m 0 :=
  fun G => ⟨∅, by simp, isRegularOn_empty G⟩

/-- `RegProp` is monotone in the number of vertices. -/
theorem regProp_mono {m m' n : ℕ} (h : m ≤ m') (hm : RegProp m n) : RegProp m' n := by
  classical
  intro G
  obtain ⟨S, hcard, d, hd⟩ := hm (G.comap (Fin.castLEEmb h))
  refine ⟨S.map (Fin.castLEEmb h), by rwa [Finset.card_map], d, ?_⟩
  intro v hv
  simp only [Finset.mem_map] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have hmapfilter : (S.map (Fin.castLEEmb h)).filter (fun w => G.Adj (Fin.castLEEmb h x) w)
      = (S.filter (fun u => (G.comap (Fin.castLEEmb h)).Adj x u)).map (Fin.castLEEmb h) := by
    rw [Finset.filter_map]
    rfl
  rw [hmapfilter, Finset.card_map]
  exact hd x hx

/-- `RegProp` is antitone in the size of the regular subgraph demanded. -/
theorem regProp_antitone_right {m n n' : ℕ} (h : n' ≤ n) (hm : RegProp m n) :
    RegProp m n' := by
  intro G
  obtain ⟨S, hcard, hreg⟩ := hm G
  exact ⟨S, h.trans hcard, hreg⟩

/-- A regular induced subgraph on `n` vertices of a graph on `m` vertices forces `n ≤ m`. -/
theorem regProp_bound {m n : ℕ} (h : RegProp m n) : n ≤ m := by
  obtain ⟨S, hcard, -⟩ := h ⊥
  have := S.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

/-- There is no room for a regular induced subgraph bigger than the whole graph. -/
theorem not_regProp_of_lt {m n : ℕ} (h : m < n) : ¬ RegProp m n :=
  fun hc => absurd (regProp_bound hc) (Nat.not_le.mpr h)

section Thresholds

/-- The set of sizes guaranteed on `m` vertices is nonempty. -/
theorem regGuarantee_set_nonempty (m : ℕ) : {n : ℕ | RegProp m n}.Nonempty :=
  ⟨0, regProp_zero m⟩

/-- The set of sizes guaranteed on `m` vertices is bounded above by `m`. -/
theorem regGuarantee_set_bddAbove (m : ℕ) : BddAbove {n : ℕ | RegProp m n} :=
  ⟨m, fun _ hn => regProp_bound hn⟩

/-- `F(m) ≤ m`: a graph on `m` vertices has at most `m` vertices to offer. -/
theorem regGuarantee_le (m : ℕ) : regGuarantee m ≤ m :=
  csSup_le (regGuarantee_set_nonempty m) (fun _ hn => regProp_bound hn)

/-- `F(m)` is itself guaranteed: every graph on `m` vertices has a regular induced
subgraph on at least `F(m)` vertices. -/
theorem regProp_regGuarantee (m : ℕ) : RegProp m (regGuarantee m) :=
  Nat.sSup_mem (regGuarantee_set_nonempty m) (regGuarantee_set_bddAbove m)

/-- Anything guaranteed on `m` vertices is at most `F(m)`. -/
theorem le_regGuarantee_of_regProp {m n : ℕ} (h : RegProp m n) : n ≤ regGuarantee m :=
  le_csSup (regGuarantee_set_bddAbove m) h

/-- If `m` vertices suffice for a regular induced subgraph on `n` vertices then
`G(n) ≤ m`. -/
theorem regThreshold_le_of_regProp {m n : ℕ} (h : RegProp m n) : regThreshold n ≤ m :=
  Nat.sInf_le h

/-- The set of vertex counts that suffice for `n` is nonempty, by Ramsey's theorem. -/
theorem regThreshold_set_nonempty (n : ℕ) : {m : ℕ | RegProp m n}.Nonempty :=
  ⟨ramsey n n, regProp_of_ramseyProp (ramseyProp_ramsey n n)⟩

/-- `G(n)` vertices really do suffice. -/
theorem regProp_regThreshold (n : ℕ) : RegProp (regThreshold n) n :=
  Nat.sInf_mem (regThreshold_set_nonempty n)

end Thresholds

end Erdos82
