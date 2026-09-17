import MerLeanExperiment.Defs

/-!
# The Sørensen–Thomassen counterexample for `m = 5`

Bollobás–Erdős asked whether every graph on `1 + n (m - 1)` vertices with `1 + n·C(m,2)` edges
contains two vertices joined by `m` internally vertex-disjoint paths.  For `m = 5` this fails:
Sørensen–Thomassen (1974) exhibit a graph on `17 = 1 + 4·4` vertices with `41 = 1 + 4·C(5,2)`
edges in which no two vertices are joined by five internally disjoint paths (`k₅(17) = 42`).

Graph data (a public mathematical object due to Sørensen–Thomassen) and the separator strategy
follow plby/lean-proofs `Erdos915` (that file carries no license header) and PR #739; the
proof below is written against the `Erdos915.HasVertexRails` interface of `MerLeanExperiment.Defs`.

The adjacency data was independently re-verified in Python before formalization: the 41 listed
pairs are distinct and loopless, the degree sequence is `(10, 8, 8, 4^14)` summing to `82 = 2·41`,
and for each of the `C(17,2) = 136` vertex pairs a unit-capacity max-flow on the vertex-split
digraph (Edmonds–Karp; interior vertices capacity 1, edges capacity 1) returns at most `4`, with
`4` attained.  The same script checked the three cut certificates used below.

Structure of the proof.  Only the vertices `0, 1, 2` have degree `≥ 5`, and the second vertices
of five internally disjoint `u`–`v` paths are five distinct neighbours of `u`, so both endpoints
must lie in `{0, 1, 2}`.  For each of the three pairs there is a three-element set `S` and a
two-colouring of `V \ S` whose only bichromatic edge is the direct edge `uv`; hence every `u`–`v`
path either has length `≤ 1` or meets `S` in an interior vertex, and internal disjointness injects
the five paths into `Option S`, of size `4`.
-/

namespace Erdos915

open SimpleGraph

/-! ## Generic lemmas about families of internally disjoint paths -/

/-- The second vertices of internally disjoint `u`–`v` paths are distinct neighbours of `u`,
so `m` internally disjoint `u`–`v` paths force `m ≤ deg u`. -/
theorem card_le_degree_of_rails {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {u v : V} {m : ℕ} (huv : u ≠ v) (p : Fin m → G.Walk u v)
    (hinj : Function.Injective p) (hpath : ∀ i, (p i).IsPath)
    (hdisj : ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j)) :
    m ≤ G.degree u := by
  classical
  have hnil : ∀ i, ¬ (p i).Nil := fun _ ↦ SimpleGraph.Walk.not_nil_of_ne huv
  have hmem : ∀ i, (p i).snd ∈ (p i).support := fun i ↦
    List.mem_of_mem_tail ((p i).snd_mem_tail_support (hnil i))
  let f : Fin m → G.neighborSet u := fun i ↦ ⟨(p i).snd, (p i).adj_snd (hnil i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hs : (p i).snd = (p j).snd := congrArg Subtype.val hij
    by_cases hv : (p i).snd = v
    · have hshort : ∀ k : Fin m, (p k).snd = v → (p k).length ≤ 1 := by
        intro k hk
        have he : s(u, v) ∈ (p k).edges := by
          simpa [hk] using (p k).mk_start_snd_mem_edges (hnil k)
        exact ((hpath k).length_eq_one_of_mem_edges he).le
      exact hinj (SimpleGraph.Walk.eq_of_length_le_one (hshort i hv)
        (hshort j (hs.symm.trans hv)))
    · by_contra hne
      rcases hdisj i j hne _ (hmem i) (hs ▸ hmem j) with h | h
      · exact ((p i).adj_snd (hnil i)).ne' h
      · exact hv h
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf

/-- Reversing every member of a family of internally disjoint `u`–`v` paths gives a family of
internally disjoint `v`–`u` paths. -/
theorem rails_reverse {V : Type*} {G : SimpleGraph V} {u v : V} {m : ℕ}
    (p : Fin m → G.Walk u v) (hinj : Function.Injective p) (hpath : ∀ i, (p i).IsPath)
    (hdisj : ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j)) :
    Function.Injective (fun i ↦ (p i).reverse) ∧ (∀ i, ((p i).reverse).IsPath) ∧
      ∀ i j, i ≠ j → InternallyDisjoint ((p i).reverse) ((p j).reverse) := by
  refine ⟨fun i j hij ↦ hinj (SimpleGraph.Walk.reverse_injective hij),
    fun i ↦ (hpath i).reverse, ?_⟩
  intro i j hne w hw hw'
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw hw'
  exact (hdisj i j hne w hw hw').symm

/-- A walk avoiding the vertex set `S` and not using the edge `e` cannot change side of a
two-colouring whose only bichromatic edge outside `S` is `e`. -/
theorem side_eq_of_avoids {V : Type*} {G : SimpleGraph V} (S : Finset V) (e : Sym2 V)
    (side : V → Bool)
    (hcut : ∀ x y : V, G.Adj x y → x ∉ S → y ∉ S → s(x, y) ≠ e → side x = side y)
    {a b : V} (w : G.Walk a b) (havoid : ∀ x ∈ w.support, x ∉ S) (he : e ∉ w.edges) :
    side a = side b := by
  induction w with
  | nil => rfl
  | @cons a c b hac w ih =>
    have h1 : side a = side c :=
      hcut a c hac (havoid a (by simp)) (havoid c (by simp)) (fun h ↦ he (by simp [h]))
    exact h1.trans (ih (fun x hx ↦ havoid x (by simp [hx])) (fun h ↦ he (by simp [h])))

/-- If `S` and a two-colouring separate `u` from `v` except across the edge `uv`, then every
`u`–`v` path either has length at most one or has an interior vertex in `S`. -/
theorem length_le_one_or_interior_mem {V : Type*} {G : SimpleGraph V} {u v : V}
    (S : Finset V) (side : V → Bool) (hu : u ∉ S) (hv : v ∉ S) (hside : side u ≠ side v)
    (hcut : ∀ x y : V, G.Adj x y → x ∉ S → y ∉ S → s(x, y) ≠ s(u, v) →
      side x = side y) {p : G.Walk u v} (hp : p.IsPath) :
    p.length ≤ 1 ∨ ∃ x ∈ S, x ∈ p.support ∧ x ≠ u ∧ x ≠ v := by
  by_cases he : s(u, v) ∈ p.edges
  · exact Or.inl (hp.length_eq_one_of_mem_edges he).le
  · refine Or.inr ?_
    by_contra hn
    have havoid : ∀ x ∈ p.support, x ∉ S := by
      intro x hx hxS
      by_cases hxu : x = u
      · exact hu (hxu ▸ hxS)
      by_cases hxv : x = v
      · exact hv (hxv ▸ hxS)
      exact hn ⟨x, hxS, hx, hxu, hxv⟩
    exact hside (side_eq_of_avoids S s(u, v) side hcut p havoid he)

/-- At most one member of an internally disjoint family has length `≤ 1`, and the others occupy
distinct vertices of a hitting set `S`, so the family has at most `S.card + 1` members. -/
theorem card_le_of_hitting_set {V : Type*} {G : SimpleGraph V} {u v : V} {m : ℕ}
    (p : Fin m → G.Walk u v) (hinj : Function.Injective p)
    (hdisj : ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j)) (S : Finset V)
    (hhit : ∀ i, (p i).length ≤ 1 ∨
      ∃ x ∈ S, x ∈ (p i).support ∧ x ≠ u ∧ x ≠ v) :
    m ≤ S.card + 1 := by
  classical
  have pick : ∀ i : Fin m, ∃ s : Option {x // x ∈ S}, (s = none → (p i).length ≤ 1) ∧
      ∀ x : {x // x ∈ S}, s = some x →
        (x : V) ∈ (p i).support ∧ (x : V) ≠ u ∧ (x : V) ≠ v := by
    intro i
    rcases hhit i with h | ⟨x, hxS, hx⟩
    · exact ⟨none, fun _ ↦ h, by simp⟩
    · exact ⟨some ⟨x, hxS⟩, by simp,
        fun y hy ↦ by simpa using (Option.some_inj.mp hy) ▸ hx⟩
  choose slot hnone hsome using pick
  have hslot : Function.Injective slot := by
    intro i j hij
    cases hs : slot i with
    | none => exact hinj (SimpleGraph.Walk.eq_of_length_le_one (hnone i hs)
        (hnone j (hij.symm.trans hs)))
    | some x =>
      by_contra hne
      obtain ⟨hxi, hxu, hxv⟩ := hsome i x hs
      obtain ⟨hxj, -, -⟩ := hsome j x (hij.symm.trans hs)
      rcases hdisj i j hne _ hxi hxj with h | h
      · exact hxu h
      · exact hxv h
  simpa using Fintype.card_le_of_injective slot hslot

/-! ## The explicit graph -/

/-- The 41 edges of the Sørensen–Thomassen graph, listed as ordered pairs. -/
def counterEdges : List (Fin 17 × Fin 17) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 13), (0, 14),
   (1, 2), (1, 3), (1, 4), (1, 9), (1, 10), (1, 11), (1, 12),
   (2, 9), (2, 10), (2, 13), (2, 14), (2, 15), (2, 16),
   (3, 5), (3, 8), (4, 6), (4, 7), (5, 6), (5, 7), (6, 8), (7, 8),
   (9, 11), (9, 12), (10, 11), (10, 12), (11, 12),
   (13, 15), (13, 16), (14, 15), (14, 16), (15, 16)]

/-- The counterexample: distinct `x, y : Fin 17` are adjacent when `counterEdges` lists the
pair in one of its two orders. -/
def counterGraph : SimpleGraph (Fin 17) where
  Adj x y := x ≠ y ∧ ((x, y) ∈ counterEdges ∨ (y, x) ∈ counterEdges)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Adjacency in `counterGraph` is decidable by list membership. -/
instance counterGraph_decidableAdj : DecidableRel counterGraph.Adj := fun x y ↦
  inferInstanceAs (Decidable (x ≠ y ∧ ((x, y) ∈ counterEdges ∨ (y, x) ∈ counterEdges)))

set_option maxRecDepth 20000

/-- The counterexample has exactly `41` edges. -/
theorem counterGraph_card_edges : counterGraph.edgeSet.ncard = 41 := by
  rw [Set.ncard_eq_toFinset_card']
  decide +kernel

/-- Every vertex other than `0`, `1`, `2` has degree `4`, hence cannot be an endpoint of five
internally disjoint paths. -/
theorem counterGraph_degree_eq_four (x : Fin 17) (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) :
    counterGraph.degree x = 4 := by
  revert x
  decide +kernel

/-! ## The three cut certificates -/

/-- No five internally disjoint `u`–`v` paths exist once a three-element `S` and a two-colouring
separate `u` from `v` across the single edge `uv`. -/
theorem no_five_of_separator {u v : Fin 17} (S : Finset (Fin 17)) (side : Fin 17 → Bool)
    (hcard : S.card = 3) (hu : u ∉ S) (hv : v ∉ S) (hside : side u ≠ side v)
    (hcut : ∀ x y : Fin 17, counterGraph.Adj x y → x ∉ S → y ∉ S →
      s(x, y) ≠ s(u, v) → side x = side y) :
    ¬ ∃ p : Fin 5 → counterGraph.Walk u v, Function.Injective p ∧ (∀ i, (p i).IsPath) ∧
      ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j) := by
  rintro ⟨p, hinj, hpath, hdisj⟩
  have h := card_le_of_hitting_set p hinj hdisj S fun i ↦
    length_le_one_or_interior_mem S side hu hv hside hcut (hpath i)
  omega

/-- The pair `(0, 1)` is cut by `{2, 3, 4}`, the side of `0` being `{0, 3, 4, 5, 6, 7, 8}`. -/
theorem no_five_zero_one :
    ¬ ∃ p : Fin 5 → counterGraph.Walk 0 1, Function.Injective p ∧ (∀ i, (p i).IsPath) ∧
      ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j) :=
  no_five_of_separator {2, 3, 4} (fun x ↦ decide (x ∈ ({1, 9, 10, 11, 12} : Finset (Fin 17))))
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

/-- The pair `(1, 2)` is cut by `{0, 9, 10}`, the side of `2` being `{2, 13, 14, 15, 16}`. -/
theorem no_five_one_two :
    ¬ ∃ p : Fin 5 → counterGraph.Walk 1 2, Function.Injective p ∧ (∀ i, (p i).IsPath) ∧
      ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j) :=
  no_five_of_separator {0, 9, 10} (fun x ↦ decide (x ∈ ({2, 13, 14, 15, 16} : Finset (Fin 17))))
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

/-- The pair `(2, 0)` is cut by `{1, 13, 14}`, the side of `0` being `{0, 3, 4, 5, 6, 7, 8}`. -/
theorem no_five_two_zero :
    ¬ ∃ p : Fin 5 → counterGraph.Walk 2 0, Function.Injective p ∧ (∀ i, (p i).IsPath) ∧
      ∀ i j, i ≠ j → InternallyDisjoint (p i) (p j) :=
  no_five_of_separator {1, 13, 14}
    (fun x ↦ decide (x ∈ ({0, 3, 4, 5, 6, 7, 8} : Finset (Fin 17))))
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

/-! ## The counterexample -/

/-- No two vertices of `counterGraph` are joined by five internally disjoint paths. -/
theorem counterGraph_not_hasVertexRails_five : ¬ HasVertexRails counterGraph 5 := by
  rintro ⟨u, v, huv, p, hinj, hpath, hdisj⟩
  obtain ⟨hinj', hpath', hdisj'⟩ := rails_reverse p hinj hpath hdisj
  have hu : u = 0 ∨ u = 1 ∨ u = 2 := by
    by_contra hn
    have hd := counterGraph_degree_eq_four u (by tauto) (by tauto) (by tauto)
    have hb := card_le_degree_of_rails huv p hinj hpath hdisj
    omega
  have hv : v = 0 ∨ v = 1 ∨ v = 2 := by
    by_contra hn
    have hd := counterGraph_degree_eq_four v (by tauto) (by tauto) (by tauto)
    have hb := card_le_degree_of_rails huv.symm _ hinj' hpath' hdisj'
    omega
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact huv rfl
  · exact no_five_zero_one ⟨p, hinj, hpath, hdisj⟩
  · exact no_five_two_zero ⟨_, hinj', hpath', hdisj'⟩
  · exact no_five_zero_one ⟨_, hinj', hpath', hdisj'⟩
  · exact huv rfl
  · exact no_five_one_two ⟨p, hinj, hpath, hdisj⟩
  · exact no_five_two_zero ⟨p, hinj, hpath, hdisj⟩
  · exact no_five_one_two ⟨_, hinj', hpath', hdisj'⟩
  · exact huv rfl

/-- The `m = 5` instance of the Bollobás–Erdős conjecture fails, with `n = 4`. -/
theorem exists_no_vertex_rails_five :
    ∃ (n : ℕ) (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      1 ≤ n ∧ Fintype.card V = 1 + n * (5 - 1) ∧
        G.edgeSet.ncard = 1 + n * Nat.choose 5 2 ∧ ¬ HasVertexRails G 5 :=
  ⟨4, Fin 17, inferInstance, counterGraph, by norm_num, by decide,
    by rw [counterGraph_card_edges]; rfl, counterGraph_not_hasVertexRails_five⟩

end Erdos915
