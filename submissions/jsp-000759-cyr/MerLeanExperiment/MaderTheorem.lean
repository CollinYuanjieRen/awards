import Mathlib
import MerLeanExperiment.Defs
import MerLeanExperiment.EdgeMenger

/-!
# Mader's theorem on edge-disjoint paths (Satz 1 of Mader 1973)

This file proves W. Mader, *Ein Extremalproblem des Zusammenhangs von Graphen*, Math. Z. **131**
(1973) 223–231, Satz 1: a finite simple graph `G` on `N ≥ m` vertices with
`2|E| + σ_m(G) > m(N-1)` contains two vertices joined by `m` edge-disjoint paths, where
`σ_m(G) = e_0(G) + ⋯ + e_{m-2}(G)` and `e_r(G)` is the number of vertices of degree at most `r`.

The route is Mader's own induction on `N`, recast so that *every* connectivity statement is a
statement about **minimum vertex-set cuts** (`minCut`) rather than about paths.  Menger's theorem
(`MerLeanExperiment.EdgeMenger`) is then used exactly once, at the very end, to convert
`m ≤ minCut G x y` into `m` edge-disjoint `x`–`y` paths.
-/

universe u

namespace Erdos915

open SimpleGraph Finset

variable {V : Type*}

section Cuts

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The ordered pairs of adjacent vertices with first entry in `S` and second entry outside `S`;
these represent the edges of `G` leaving `S`, each exactly once. -/
def cutPairs (S : Finset V) : Finset (V × V) := (S ×ˢ Sᶜ).filter fun p ↦ G.Adj p.1 p.2

/-- The number of edges of `G` with exactly one endpoint in `S`. -/
def cutSize (S : Finset V) : ℕ := (cutPairs G S).card

variable {G}

/-- Membership in `cutPairs`. -/
@[simp] lemma mem_cutPairs {S : Finset V} {p : V × V} :
    p ∈ cutPairs G S ↔ p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2 := by
  simp only [cutPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_compl]
  tauto

/-- `cutPairs` described by an indicator over all adjacent ordered pairs. -/
lemma cutSize_eq_sum_indicator (S : Finset V) :
    cutSize G S =
      ∑ p ∈ (Finset.univ : Finset (V × V)).filter (fun p ↦ G.Adj p.1 p.2),
        if p.1 ∈ S ∧ p.2 ∉ S then 1 else 0 := by
  rw [cutSize, ← Finset.card_filter]
  congr 1
  ext p
  simp only [mem_cutPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The cut size as a sum of outside-degrees. -/
lemma cutSize_eq_sum_sdiff (S : Finset V) :
    cutSize G S = ∑ x ∈ S, (G.neighborFinset x \ S).card := by
  rw [cutSize, cutPairs, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.card_filter]
  congr 1
  ext y
  simp [Finset.mem_sdiff, and_comm]

/-- Complementing a vertex set does not change the cut size. -/
lemma cutSize_compl (S : Finset V) : cutSize G Sᶜ = cutSize G S := by
  rw [cutSize_eq_sum_indicator, cutSize_eq_sum_indicator]
  refine Finset.sum_equiv (Equiv.prodComm V V) (fun p ↦ ?_) (fun p _ ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodComm_apply,
      Prod.fst_swap, Prod.snd_swap]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  · simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Finset.mem_compl,
      not_not]
    by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.2 ∈ S <;> simp [h1, h2]

/-- The cut function is submodular. -/
lemma cutSize_submodular (S T : Finset V) :
    cutSize G (S ∩ T) + cutSize G (S ∪ T) ≤ cutSize G S + cutSize G T := by
  simp only [cutSize_eq_sum_indicator]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  by_cases h1 : p.1 ∈ S <;> by_cases h2 : p.1 ∈ T <;> by_cases h3 : p.2 ∈ S <;>
    by_cases h4 : p.2 ∈ T <;>
    simp [Finset.mem_inter, Finset.mem_union, h1, h2, h3, h4]

/-- The cut around a single vertex is its degree. -/
lemma cutSize_singleton (x : V) : cutSize G {x} = G.degree x := by
  rw [cutSize_eq_sum_sdiff, Finset.sum_singleton]
  have h : G.neighborFinset x \ {x} = G.neighborFinset x := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_singleton, mem_neighborFinset]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.ne'⟩⟩
  rw [h, G.card_neighborFinset_eq_degree]

variable (G)

/-- `minCut G x y` is the least number of edges whose removal separates `x` from `y`, presented
as the least size of a vertex set containing `y` but not `x`. -/
noncomputable def minCut (x y : V) : ℕ := sInf {k | ∃ S : Finset V, x ∉ S ∧ y ∈ S ∧ cutSize G S = k}

variable {G}

/-- Any separating vertex set bounds `minCut`. -/
lemma minCut_le {x y : V} {S : Finset V} (hx : x ∉ S) (hy : y ∈ S) :
    minCut G x y ≤ cutSize G S :=
  Nat.sInf_le ⟨S, hx, hy, rfl⟩

/-- `minCut` is attained. -/
lemma exists_cutSize_eq_minCut {x y : V} (hxy : x ≠ y) :
    ∃ S : Finset V, x ∉ S ∧ y ∈ S ∧ cutSize G S = minCut G x y := by
  have hne : {k : ℕ | ∃ S : Finset V, x ∉ S ∧ y ∈ S ∧ cutSize G S = k}.Nonempty :=
    ⟨cutSize G {y}, ({y} : Finset V), by simp [hxy], by simp, rfl⟩
  exact Nat.sInf_mem hne

/-- `minCut` is symmetric. -/
lemma minCut_comm (x y : V) : minCut G x y = minCut G y x := by
  have key : ∀ a b : V, minCut G a b ≤ minCut G b a := by
    intro a b
    rcases eq_or_ne b a with rfl | hba
    · exact le_rfl
    · obtain ⟨S, hbS, haS, hS⟩ := exists_cutSize_eq_minCut (G := G) hba
      refine le_trans (minCut_le (S := Sᶜ) ?_ ?_) (le_of_eq ?_)
      · simpa using haS
      · simpa using hbS
      · rw [cutSize_compl, hS]
  exact le_antisymm (key x y) (key y x)

/-- `minCut` never exceeds a degree. -/
lemma minCut_le_degree {x y : V} (hxy : x ≠ y) : minCut G x y ≤ G.degree x := by
  refine le_trans (minCut_le (S := ({x} : Finset V)ᶜ) (by simp) (by simp [hxy.symm])) ?_
  rw [cutSize_compl, cutSize_singleton]

/-- If no vertex set of cut size `< k` separates `x` from `y`, then `x` and `y` are
`k`-edge-reachable.  (This is the *easy* half of the min-cut description of edge connectivity;
it needs no form of Menger's theorem.) -/
lemma isEdgeReachable_of_le_minCut {x y : V} {k : ℕ} (h : k ≤ minCut G x y) :
    G.IsEdgeReachable k x y := by
  classical
  intro s hs
  by_contra hcon
  have hfin : s.Finite := Set.finite_of_encard_le_coe (le_of_lt hs)
  set S : Finset V := Finset.univ.filter (fun v ↦ ¬ (G.deleteEdges s).Reachable x v) with hSdef
  have hxS : x ∉ S := by simp [hSdef]
  have hyS : y ∈ S := by simpa [hSdef] using hcon
  have hmaps : ∀ p ∈ cutPairs G S, s(p.1, p.2) ∈ hfin.toFinset := by
    intro p hp
    rw [mem_cutPairs] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    rw [Set.Finite.mem_toFinset]
    by_contra hmem
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h1 h2
    have hadj : (G.deleteEdges s).Adj p.1 p.2 := by
      rw [deleteEdges_adj]; exact ⟨h3, hmem⟩
    exact h1 (h2.trans hadj.symm.reachable)
  have hinj : Set.InjOn (fun p : V × V ↦ s(p.1, p.2)) (cutPairs G S) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, mem_cutPairs] at hp hq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ hp.1) hq.2.1
  have hle : cutSize G S ≤ hfin.toFinset.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hcard : (hfin.toFinset.card : ℕ∞) < k := by
    rw [← hfin.encard_eq_coe_toFinset_card]; exact hs
  have hcard' : hfin.toFinset.card < k := by exact_mod_cast hcard
  exact absurd (le_trans h (minCut_le hxS hyS)) (by omega)

end Cuts

section Sigma

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `σ_m(G) = e_0(G) + ⋯ + e_{m-2}(G) = ∑_x (m-1-deg x)`. -/
lemma sum_lowDegreeCount (m : ℕ) :
    ∑ r ∈ Finset.range (m - 1), lowDegreeCount G r = ∑ x : V, (m - 1 - G.degree x) := by
  classical
  simp only [lowDegreeCount, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← Finset.card_filter]
  have hIco : (Finset.range (m - 1)).filter (fun r ↦ G.degree x ≤ r)
      = Finset.Ico (G.degree x) (m - 1) := by
    ext r
    simp [Finset.mem_Ico, and_comm]
  rw [hIco, Nat.card_Ico]

/-- The edge set cardinality as a `Finset` card. -/
lemma ncard_edgeSet_eq : G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

/-- The key identity `2|E| + σ_m(G) = ∑_x max (deg x) (m-1)`. -/
lemma sumMax_eq_two_mul_card_edges_add_sigma (m : ℕ) :
    ∑ x : V, max (G.degree x) (m - 1)
      = 2 * G.edgeSet.ncard + ∑ r ∈ Finset.range (m - 1), lowDegreeCount G r := by
  classical
  rw [sum_lowDegreeCount, ncard_edgeSet_eq, ← G.sum_degrees_eq_twice_card_edges,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  omega

end Sigma

section Reductions

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbours of `x` lying outside `A`. -/
def outDeg (A : Finset V) (x : V) : ℕ := (G.neighborFinset x \ A).card

/-- The vertices of `A` having at least one neighbour outside `A`. -/
def boundary (A : Finset V) : Finset V := A.filter fun x ↦ 0 < outDeg G A x

variable {G}

/-- Membership in `boundary`. -/
@[simp] lemma mem_boundary {A : Finset V} {x : V} :
    x ∈ boundary G A ↔ x ∈ A ∧ 0 < outDeg G A x := by
  simp [boundary]

/-- `boundary G A ⊆ A`. -/
lemma boundary_subset (A : Finset V) : boundary G A ⊆ A := Finset.filter_subset _ _

/-- The cut around `A` is the total outside-degree of `A`. -/
lemma cutSize_eq_sum_outDeg (A : Finset V) : cutSize G A = ∑ x ∈ A, outDeg G A x :=
  cutSize_eq_sum_sdiff A

/-- The boundary is no larger than the cut. -/
lemma card_boundary_le_cutSize (A : Finset V) : (boundary G A).card ≤ cutSize G A := by
  rw [cutSize_eq_sum_outDeg, ← Finset.sum_filter_add_sum_filter_not A fun x ↦ 0 < outDeg G A x]
  have h1 : (boundary G A).card ≤ ∑ x ∈ A.filter fun x ↦ 0 < outDeg G A x, outDeg G A x := by
    rw [boundary, Finset.card_eq_sum_ones (A.filter fun x ↦ 0 < outDeg G A x)]
    exact Finset.sum_le_sum fun x hx ↦ (Finset.mem_filter.mp hx).2
  omega

/-- Splitting the degree of `x` along `A`. -/
lemma degree_eq_inter_add_outDeg (A : Finset V) (x : V) :
    G.degree x = (G.neighborFinset x ∩ A).card + outDeg G A x := by
  rw [outDeg, Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]

variable (G)

/-- The subgraph of `G` induced on a finite vertex set `D`. -/
def sub (D : Finset V) : SimpleGraph {x // x ∈ D} := SimpleGraph.comap Subtype.val G

instance instDecidableSubAdj (D : Finset V) : DecidableRel (sub G D).Adj := fun _ _ ↦
  inferInstanceAs (Decidable (G.Adj _ _))

variable {G}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Adjacency in the induced subgraph. -/
@[simp] lemma sub_adj {D : Finset V} {a b : {x // x ∈ D}} :
    (sub G D).Adj a b ↔ G.Adj (a : V) (b : V) := Iff.rfl

omit [DecidableEq V] in
/-- A vertex all of whose neighbours lie in `D` keeps its degree in the induced subgraph. -/
lemma degree_sub_eq {D : Finset V} (a : {x // x ∈ D})
    (h : ∀ y : V, G.Adj (a : V) y → y ∈ D) : (sub G D).degree a = G.degree (a : V) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun v _ ↦ (v : V)) ?_ ?_ ?_
  · intro v hv
    rw [mem_neighborFinset] at hv ⊢
    exact hv
  · intro v1 _ v2 _ heq
    exact Subtype.ext heq
  · intro y hy
    rw [mem_neighborFinset] at hy
    exact ⟨⟨y, h y hy⟩, by rw [mem_neighborFinset]; exact hy, rfl⟩

/-- Cuts of the induced subgraph come from cuts of `G`. -/
lemma minCut_sub_le {D : Finset V} (u v : {x // x ∈ D}) (huv : (u : V) ≠ (v : V)) :
    minCut (sub G D) u v ≤ minCut G (u : V) (v : V) := by
  obtain ⟨S, huS, hvS, hS⟩ := exists_cutSize_eq_minCut (G := G) huv
  set S' : Finset {x // x ∈ D} := Finset.univ.filter (fun w ↦ (w : V) ∈ S) with hS'
  have huS' : u ∉ S' := by simp [hS', huS]
  have hvS' : v ∈ S' := by simp [hS', hvS]
  refine le_trans (minCut_le huS' hvS') ?_
  rw [← hS, cutSize, cutSize]
  refine Finset.card_le_card_of_injOn (fun p ↦ ((p.1 : V), (p.2 : V))) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, mem_cutPairs] at hp
    simp only [Finset.mem_coe, mem_cutPairs]
    obtain ⟨h1, h2, h3⟩ := hp
    simp only [hS', Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact ⟨h1, h2, h3⟩
  · intro p _ q _ hpq
    rw [Prod.ext_iff] at hpq ⊢
    exact ⟨Subtype.ext hpq.1, Subtype.ext hpq.2⟩

variable (G)

/-- The relation from which the apex contraction of `G` along `A` is built. -/
def contractRel (A : Finset V) : Option {x // x ∈ A} → Option {x // x ∈ A} → Prop
  | some x, some y => G.Adj (x : V) (y : V)
  | some x, none => (x : V) ∈ boundary G A
  | none, _ => False

instance instDecidableContractRel (A : Finset V) : DecidableRel (contractRel G A) := by
  intro a b
  match a, b with
  | some x, some y => exact inferInstanceAs (Decidable (G.Adj (x : V) (y : V)))
  | some x, none => exact inferInstanceAs (Decidable ((x : V) ∈ boundary G A))
  | none, b => exact inferInstanceAs (Decidable False)

/-- `contract G A` is `G` with everything outside `A` contracted to a single apex vertex. -/
def contract (A : Finset V) : SimpleGraph (Option {x // x ∈ A}) :=
  SimpleGraph.fromRel (contractRel G A)

instance instDecidableContractAdj (A : Finset V) : DecidableRel (contract G A).Adj := fun a b ↦
  decidable_of_iff _ (SimpleGraph.fromRel_adj (contractRel G A) a b).symm

variable {G}

/-- Adjacency of two old vertices in the contraction. -/
@[simp] lemma contract_adj_some_some {A : Finset V} (x y : {x // x ∈ A}) :
    (contract G A).Adj (some x) (some y) ↔ G.Adj (x : V) (y : V) := by
  rw [contract, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    refine ⟨fun hc ↦ h.ne (congrArg Subtype.val (Option.some.inj hc)), Or.inl h⟩

/-- Adjacency of an old vertex with the apex. -/
@[simp] lemma contract_adj_some_none {A : Finset V} (x : {x // x ∈ A}) :
    (contract G A).Adj (some x) none ↔ (x : V) ∈ boundary G A := by
  rw [contract, SimpleGraph.fromRel_adj]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  exact ⟨fun h ↦ h.elim id (fun h ↦ h.elim), fun h ↦ Or.inl h⟩

/-- Adjacency of the apex with an old vertex. -/
@[simp] lemma contract_adj_none_some {A : Finset V} (y : {x // x ∈ A}) :
    (contract G A).Adj none (some y) ↔ (y : V) ∈ boundary G A := by
  rw [SimpleGraph.adj_comm]
  exact contract_adj_some_none y

/-- The apex is not adjacent to itself. -/
@[simp] lemma contract_adj_none_none {A : Finset V} :
    ¬ (contract G A).Adj (none : Option {x // x ∈ A}) none := (contract G A).irrefl

variable (G)

/-- A chosen neighbour of `x` outside `A`. -/
noncomputable def outNbr (A : Finset V) (x : V) : V :=
  if h : (G.neighborFinset x \ A).Nonempty then h.choose else x

variable {G}

/-- The chosen outside neighbour really is one, provided there is any. -/
lemma outNbr_spec {A : Finset V} {x : V} (h : 0 < outDeg G A x) :
    G.Adj x (outNbr G A x) ∧ outNbr G A x ∉ A := by
  have hne : (G.neighborFinset x \ A).Nonempty := Finset.card_pos.mp h
  rw [outNbr, dite_eq_left hne]
  have := hne.choose_spec
  rw [Finset.mem_sdiff, mem_neighborFinset] at this
  exact this

/-- The degree of the apex vertex is the size of the boundary. -/
lemma degree_contract_none (A : Finset V) :
    (contract G A).degree none = (boundary G A).card := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_option]
  simp only [contract_adj_none_none, contract_adj_none_some, ite_false, zero_add]
  have h1 : ∑ y : {x // x ∈ A}, (if (y : V) ∈ boundary G A then 1 else 0)
      = ∑ x ∈ A, (if x ∈ boundary G A then 1 else 0) := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach A (fun z ↦ (if z ∈ boundary G A then 1 else 0 : ℕ))
  rw [h1, ← Finset.card_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (boundary_subset A)]

/-- The degree of an old vertex in the contraction. -/
lemma degree_contract_some (A : Finset V) (x : {x // x ∈ A}) :
    (contract G A).degree (some x)
      = (G.neighborFinset (x : V) ∩ A).card + (if (x : V) ∈ boundary G A then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_option]
  simp only [contract_adj_some_none, contract_adj_some_some]
  have h1 : ∑ y : {x // x ∈ A}, (if G.Adj (x : V) (y : V) then 1 else 0)
      = ∑ z ∈ A, (if G.Adj (x : V) z then 1 else 0) := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach A (fun z ↦ (if G.Adj (x : V) z then 1 else 0 : ℕ))
  rw [h1, ← Finset.card_filter]
  have h2 : A.filter (fun z ↦ G.Adj (x : V) z) = G.neighborFinset (x : V) ∩ A := by
    ext z
    simp [mem_neighborFinset, and_comm]
  rw [h2, Nat.add_comm]

/-- Degree bookkeeping for the contraction. -/
lemma degree_contract_add (A : Finset V) (x : {x // x ∈ A}) :
    G.degree (x : V) + (if (x : V) ∈ boundary G A then 1 else 0)
      = (contract G A).degree (some x) + outDeg G A (x : V) := by
  rw [degree_contract_some, degree_eq_inter_add_outDeg A (x : V)]
  omega

/-- Auxiliary form of Mader's Claim (A): a cut `S` of `G` avoiding `a₂` yields a cut of the
contraction that is no larger. -/
lemma minCut_contract_le_aux {A : Finset V} {a₁ a₂ : V} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∉ A)
    (hmin : ∀ S : Finset V, a₁ ∉ S → a₂ ∈ S → cutSize G A ≤ cutSize G S)
    (x y : {v // v ∈ A}) (S : Finset V) (hxS : (x : V) ∉ S) (hyS : (y : V) ∈ S)
    (ha₂S : a₂ ∉ S) :
    minCut (contract G A) (some x) (some y) ≤ cutSize G S := by
  have hSA : cutSize G (S ∩ A) ≤ cutSize G S := by
    have hsub := cutSize_submodular (G := G) S A
    have hun : cutSize G A ≤ cutSize G (S ∪ A) := by
      have h := hmin (S ∪ A)ᶜ (by simp [ha₁]) (by simp [ha₂S, ha₂])
      rwa [cutSize_compl] at h
    omega
  set S'' : Finset (Option {v // v ∈ A}) :=
    (Finset.filter (fun w : {v // v ∈ A} ↦ (w : V) ∈ S) Finset.univ).image some with hS''
  have hmemS'' : ∀ w : {v // v ∈ A}, ((some w : Option {v // v ∈ A}) ∈ S'' ↔ (w : V) ∈ S) := by
    intro w; simp [hS'']
  have hnoneS'' : (none : Option {v // v ∈ A}) ∉ S'' := by simp [hS'']
  have hstep : cutSize (contract G A) S'' ≤ cutSize G (S ∩ A) := by
    rw [cutSize, cutSize]
    refine Finset.card_le_card_of_injOn
      (fun p ↦ (p.1.elim a₁ (fun u ↦ (u : V)),
        p.2.elim (outNbr G A (p.1.elim a₁ (fun u ↦ (u : V)))) (fun v ↦ (v : V)))) ?_ ?_
    · rintro ⟨p1, p2⟩ hp
      rw [Finset.mem_coe, mem_cutPairs] at hp
      obtain ⟨h1, h2, h3⟩ := hp
      cases p1 with
      | none => exact absurd h1 hnoneS''
      | some u =>
        have huSA : (u : V) ∈ S ∩ A :=
          Finset.mem_inter.mpr ⟨(hmemS'' u).mp h1, u.2⟩
        cases p2 with
        | none =>
          have hb : (u : V) ∈ boundary G A := by simpa using h3
          obtain ⟨hadj, hout⟩ := outNbr_spec (mem_boundary.mp hb).2
          simp only [Finset.mem_coe, mem_cutPairs, Option.elim_some, Option.elim_none]
          exact ⟨huSA, by simp [Finset.mem_inter, hout], hadj⟩
        | some v =>
          have hvS : (v : V) ∉ S := fun hc ↦ h2 ((hmemS'' v).mpr hc)
          have hadj : G.Adj (u : V) (v : V) := by simpa using h3
          simp only [Finset.mem_coe, mem_cutPairs, Option.elim_some]
          exact ⟨huSA, by simp [Finset.mem_inter, hvS], hadj⟩
    · rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq hpq
      rw [Finset.mem_coe, mem_cutPairs] at hp hq
      cases p1 with
      | none => exact absurd hp.1 hnoneS''
      | some u =>
      cases q1 with
      | none => exact absurd hq.1 hnoneS''
      | some u' =>
      simp only [Option.elim_some, Prod.mk.injEq] at hpq
      obtain ⟨hA, hB⟩ := hpq
      have huu : u = u' := Subtype.ext hA
      subst huu
      cases p2 with
      | none =>
        have hb : (u : V) ∈ boundary G A := by simpa using hp.2.2
        obtain ⟨-, hout⟩ := outNbr_spec (mem_boundary.mp hb).2
        cases q2 with
        | none => rfl
        | some v' =>
          simp only [Option.elim_none, Option.elim_some] at hB
          exact absurd (hB ▸ v'.2) hout
      | some v =>
        cases q2 with
        | none =>
          have hb : (u : V) ∈ boundary G A := by simpa using hq.2.2
          obtain ⟨-, hout⟩ := outNbr_spec (mem_boundary.mp hb).2
          simp only [Option.elim_none, Option.elim_some] at hB
          exact absurd (hB ▸ v.2) hout
        | some v' =>
          simp only [Option.elim_some] at hB
          rw [Subtype.ext hB]
  refine le_trans (le_trans (minCut_le ?_ ((hmemS'' y).mpr hyS)) hstep) hSA
  rw [hmemS'']
  exact hxS

/-- **Claim (A)** of Mader's proof, in min-cut form: contracting the far side of a *minimum*
`a₁`–`a₂` edge cut to a single apex vertex does not increase any local edge connectivity. -/
lemma minCut_contract_le {A : Finset V} {a₁ a₂ : V} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∉ A)
    (hmin : ∀ S : Finset V, a₁ ∉ S → a₂ ∈ S → cutSize G A ≤ cutSize G S)
    (x y : {v // v ∈ A}) (hxy : (x : V) ≠ (y : V)) :
    minCut (contract G A) (some x) (some y) ≤ minCut G (x : V) (y : V) := by
  obtain ⟨S, hxS, hyS, hS⟩ := exists_cutSize_eq_minCut (G := G) hxy
  by_cases ha : a₂ ∈ S
  · have h := minCut_contract_le_aux ha₁ ha₂ hmin y x Sᶜ (by simp [hyS]) (by simp [hxS])
      (by simp [ha])
    rw [cutSize_compl, hS] at h
    rwa [minCut_comm] at h
  · have h := minCut_contract_le_aux ha₁ ha₂ hmin x y S hxS hyS ha
    rwa [hS] at h

/-- Low edge connectivity is inherited by the apex contraction along a minimum cut. -/
lemma minCut_contract_lt {A : Finset V} {a₁ a₂ : V} {m : ℕ} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∉ A)
    (hmin : ∀ S : Finset V, a₁ ∉ S → a₂ ∈ S → cutSize G A ≤ cutSize G S)
    (hbd : (boundary G A).card < m) (hlow : ∀ u v : V, u ≠ v → minCut G u v < m)
    (p q : Option {v // v ∈ A}) (hpq : p ≠ q) : minCut (contract G A) p q < m := by
  have hapex : ∀ z : {v // v ∈ A}, minCut (contract G A) none (some z) < m := by
    intro z
    refine lt_of_le_of_lt (le_trans (minCut_le_degree (by simp)) ?_) hbd
    exact le_of_eq (degree_contract_none A)
  cases p with
  | none =>
    cases q with
    | none => exact absurd rfl hpq
    | some z => exact hapex z
  | some x =>
    cases q with
    | none => rw [minCut_comm]; exact hapex x
    | some y =>
      have hxy : (x : V) ≠ (y : V) := fun hc ↦ hpq (by rw [Subtype.ext hc])
      exact lt_of_le_of_lt (minCut_contract_le ha₁ ha₂ hmin x y hxy) (hlow _ _ hxy)

/-- Low edge connectivity is inherited by induced subgraphs. -/
lemma minCut_sub_lt {D : Finset V} {m : ℕ} (hlow : ∀ u v : V, u ≠ v → minCut G u v < m)
    (p q : {x // x ∈ D}) (hpq : p ≠ q) : minCut (sub G D) p q < m := by
  have hne : (p : V) ≠ (q : V) := fun hc ↦ hpq (Subtype.ext hc)
  exact lt_of_le_of_lt (minCut_sub_le p q hne) (hlow _ _ hne)

/-- Inside `A`, a vertex has at most `A.card - 1` neighbours. -/
lemma card_inter_neighborFinset_lt {A : Finset V} {a : V} (ha : a ∈ A) :
    (G.neighborFinset a ∩ A).card + 1 ≤ A.card := by
  have hsub : G.neighborFinset a ∩ A ⊆ A.erase a := by
    intro y hy
    rw [Finset.mem_inter, mem_neighborFinset] at hy
    exact Finset.mem_erase.mpr ⟨hy.1.ne', hy.2⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_erase_of_mem ha
  have h3 : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega

/-- Splitting the degree of a vertex of `A`. -/
lemma degree_le_card_add_outDeg {A : Finset V} {a : V} (ha : a ∈ A) :
    G.degree a + 1 ≤ A.card + outDeg G A a := by
  have h1 := degree_eq_inter_add_outDeg (G := G) A a
  have h2 := card_inter_neighborFinset_lt (G := G) ha
  omega

/-- The outside-degree of a single vertex plus the boundary size is essentially the cut. -/
lemma outDeg_add_card_boundary_le {A : Finset V} {a : V} (ha : a ∈ A) :
    outDeg G A a + (boundary G A).card ≤ cutSize G A + 1 := by
  classical
  set Bd : Finset V := boundary G A with hBd
  have hsub : insert a (Bd.erase a) ⊆ A := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ha
    · exact boundary_subset A (Finset.mem_of_mem_erase hy)
  have h1 : ∑ x ∈ insert a (Bd.erase a), outDeg G A x ≤ cutSize G A := by
    rw [cutSize_eq_sum_outDeg]
    exact Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_insert (Finset.notMem_erase a Bd)] at h1
  have h2 : (Bd.erase a).card ≤ ∑ x ∈ Bd.erase a, outDeg G A x := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun x hx ↦ ?_
    exact (mem_boundary.mp (Finset.mem_of_mem_erase hx)).2
  have h3 : Bd.card ≤ (Bd.erase a).card + 1 := by
    rcases Finset.decidableMem a Bd with h | h
    · rw [Finset.erase_eq_of_notMem h]; omega
    · rw [Finset.card_erase_of_mem h]
      have : 1 ≤ Bd.card := Finset.card_pos.mpr ⟨a, h⟩
      omega
  omega

/-- The degree of a vertex of `A` plus the boundary size is bounded by `|A|` plus the cut. -/
lemma degree_add_card_boundary_le {A : Finset V} {a : V} (ha : a ∈ A) :
    G.degree a + (boundary G A).card ≤ A.card + cutSize G A := by
  have h1 := degree_le_card_add_outDeg (G := G) ha
  have h2 := outDeg_add_card_boundary_le (G := G) ha
  omega

/-- The per-side bound of Mader's proof: if `a ∈ A` has degree at least `m`, the cut around `A`
has fewer than `m` edges, and (when `A` has at least `m-1` vertices) the induction hypothesis
holds for the apex contraction along `A`, then the `A`-part of `∑ max (deg x) (m-1)` obeys
Mader's estimate. -/
lemma side_bound {m : ℕ} (hm : 2 ≤ m) {A : Finset V} {a : V} (ha : a ∈ A)
    (hdeg : m ≤ G.degree a) (ht : cutSize G A < m)
    (hcon : m ≤ A.card + 1 →
      ∑ p : Option {v // v ∈ A}, max ((contract G A).degree p) (m - 1) ≤ m * A.card) :
    ∑ x ∈ A, max (G.degree x) (m - 1) + (boundary G A).card + (m - 1)
      ≤ m * A.card + cutSize G A := by
  classical
  have hcard1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hindsum : ∑ x ∈ A, (if 0 < outDeg G A x then 1 else 0) = (boundary G A).card := by
    rw [← Finset.card_filter]
    rfl
  by_cases hbig : m ≤ A.card + 1
  · have hsum := hcon hbig
    rw [Fintype.sum_option] at hsum
    have hnone : max ((contract G A).degree none) (m - 1) = m - 1 := by
      rw [degree_contract_none]
      have := card_boundary_le_cutSize (G := G) A
      omega
    rw [hnone] at hsum
    have hkey : ∑ x ∈ A, max (G.degree x) (m - 1) + (boundary G A).card
        ≤ (∑ v : {v // v ∈ A}, max ((contract G A).degree (some v)) (m - 1)) + cutSize G A := by
      have hL : ∑ x ∈ A, (max (G.degree x) (m - 1) + (if 0 < outDeg G A x then 1 else 0))
          = ∑ x ∈ A, max (G.degree x) (m - 1) + (boundary G A).card := by
        rw [Finset.sum_add_distrib, hindsum]
      have hR : ∑ v : {v // v ∈ A},
            (max ((contract G A).degree (some v)) (m - 1) + outDeg G A (v : V))
          = (∑ v : {v // v ∈ A}, max ((contract G A).degree (some v)) (m - 1))
            + cutSize G A := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [cutSize_eq_sum_outDeg, Finset.univ_eq_attach]
        exact Finset.sum_attach A (outDeg G A)
      rw [← hL, ← hR, Finset.univ_eq_attach,
        ← Finset.sum_attach A (fun x ↦ max (G.degree x) (m - 1)
          + (if 0 < outDeg G A x then 1 else 0))]
      refine Finset.sum_le_sum fun v _ ↦ ?_
      have hi : (if (v : V) ∈ boundary G A then 1 else 0)
          = (if 0 < outDeg G A (v : V) then 1 else 0) := by
        congr 1
        simp [mem_boundary, v.2]
      have hadd : G.degree (v : V) + (if 0 < outDeg G A (v : V) then 1 else 0)
          = (contract G A).degree (some v) + outDeg G A (v : V) := by
        rw [← hi]; exact degree_contract_add A v
      rcases Nat.eq_zero_or_pos (outDeg G A (v : V)) with h0 | h0
      · rw [h0] at hadd ⊢
        simp only [lt_irrefl, ite_false, Nat.add_zero] at hadd ⊢
        omega
      · rw [ite_eq_left h0] at hadd ⊢
        omega
    omega
  · rw [Nat.not_le] at hbig
    have hpt : ∀ x ∈ A, max (G.degree x) (m - 1) + (if 0 < outDeg G A x then 1 else 0)
        ≤ (m - 1) + outDeg G A x := by
      intro x hx
      have hd := degree_le_card_add_outDeg (G := G) hx
      rcases Nat.eq_zero_or_pos (outDeg G A x) with h0 | h0
      · rw [h0] at hd ⊢
        simp only [lt_irrefl, ite_false, Nat.add_zero]
        omega
      · rw [ite_eq_left h0]
        omega
    have hpta : max (G.degree a) (m - 1) + (if 0 < outDeg G A a then 1 else 0)
        + (m - 1 - A.card) ≤ (m - 1) + outDeg G A a := by
      have hd := degree_le_card_add_outDeg (G := G) ha
      have h0 : 0 < outDeg G A a := by omega
      rw [ite_eq_left h0]
      omega
    set f : V → ℕ := fun x ↦ max (G.degree x) (m - 1) + (if 0 < outDeg G A x then 1 else 0)
      with hf
    set g : V → ℕ := fun x ↦ (m - 1) + outDeg G A x with hg
    have hsplitf : f a + ∑ x ∈ A.erase a, f x = ∑ x ∈ A, f x := Finset.add_sum_erase A f ha
    have hsplitg : g a + ∑ x ∈ A.erase a, g x = ∑ x ∈ A, g x := Finset.add_sum_erase A g ha
    have herase : ∑ x ∈ A.erase a, f x ≤ ∑ x ∈ A.erase a, g x :=
      Finset.sum_le_sum fun x hx ↦ hpt x (Finset.mem_of_mem_erase hx)
    have hfa : f a + (m - 1 - A.card) ≤ g a := hpta
    have hsumf : ∑ x ∈ A, f x
        = ∑ x ∈ A, max (G.degree x) (m - 1) + (boundary G A).card := by
      rw [hf, Finset.sum_add_distrib, hindsum]
    have hsumg : ∑ x ∈ A, g x = (m - 1) * A.card + cutSize G A := by
      rw [hg, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, cutSize_eq_sum_outDeg,
        Nat.mul_comm]
    have hmul : (m - 1) * A.card + A.card = m * A.card := by
      cases m with
      | zero => omega
      | succ k => simp [Nat.succ_mul]
    omega

/-- The vertex-deletion bound of Mader's proof: applying the induction hypothesis to the subgraph
induced on `boundary G A ∪ Aᶜ` (in which every vertex of `Aᶜ` keeps its full degree) controls the
`Aᶜ`-part of `∑ max (deg x) (m-1)`. -/
lemma del_bound {m : ℕ} (hm : 2 ≤ m) {A : Finset V} (hne : (Aᶜ : Finset V).Nonempty)
    (hIH : ∑ v : {x // x ∈ boundary G A ∪ Aᶜ},
        max ((sub G (boundary G A ∪ Aᶜ)).degree v) (m - 1)
      ≤ m * ((boundary G A ∪ Aᶜ).card - 1)) :
    ∑ x ∈ (Aᶜ : Finset V), max (G.degree x) (m - 1) + m
      ≤ (boundary G A).card + m * (Aᶜ : Finset V).card := by
  classical
  set C : Finset V := boundary G A with hC
  set D : Finset V := C ∪ Aᶜ with hD
  have hdisj : Disjoint C (Aᶜ : Finset V) := by
    rw [Finset.disjoint_right]
    intro x hx hxC
    exact (Finset.mem_compl.mp hx) (boundary_subset A hxC)
  have hDcard : D.card = C.card + (Aᶜ : Finset V).card := Finset.card_union_of_disjoint hdisj
  set h : V → ℕ := fun x ↦ if x ∈ (Aᶜ : Finset V) then max (G.degree x) (m - 1) else m - 1
    with hh
  have hsumD : ∑ x ∈ D, h x
      = ∑ x ∈ (Aᶜ : Finset V), max (G.degree x) (m - 1) + (m - 1) * C.card := by
    rw [hD, Finset.sum_union hdisj]
    have h1 : ∑ x ∈ C, h x = (m - 1) * C.card := by
      rw [Finset.sum_congr rfl (fun x hx ↦ ?_), Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      rw [hh]
      exact ite_eq_right (by simp [Finset.mem_compl, boundary_subset A hx])
    have h2 : ∑ x ∈ (Aᶜ : Finset V), h x = ∑ x ∈ (Aᶜ : Finset V), max (G.degree x) (m - 1) :=
      Finset.sum_congr rfl fun x hx ↦ ite_eq_left hx
    rw [h1, h2, Nat.add_comm]
  have hstep : ∑ x ∈ D, h x ≤ ∑ v : {x // x ∈ D}, max ((sub G D).degree v) (m - 1) := by
    rw [Finset.univ_eq_attach, ← Finset.sum_attach D h]
    refine Finset.sum_le_sum fun v _ ↦ ?_
    by_cases hv : (v : V) ∈ (Aᶜ : Finset V)
    · show (if (v : V) ∈ (Aᶜ : Finset V) then _ else _) ≤ _
      rw [ite_eq_left hv]
      have hnb : ∀ y : V, G.Adj (v : V) y → y ∈ D := by
        intro y hy
        by_cases hyA : y ∈ A
        · refine Finset.mem_union_left _ ?_
          rw [hC, mem_boundary]
          refine ⟨hyA, ?_⟩
          rw [outDeg, Finset.card_pos]
          refine ⟨(v : V), Finset.mem_sdiff.mpr ⟨?_, Finset.mem_compl.mp hv⟩⟩
          rw [mem_neighborFinset]
          exact hy.symm
        · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hyA)
      rw [degree_sub_eq v hnb]
    · show (if (v : V) ∈ (Aᶜ : Finset V) then _ else _) ≤ _
      rw [ite_eq_right hv]
      exact le_max_right _ _
  have hAc : 1 ≤ (Aᶜ : Finset V).card := Finset.card_pos.mpr hne
  have hm1 : m * (D.card - 1) + m = m * C.card + m * (Aᶜ : Finset V).card := by
    rw [← Nat.mul_add, ← Nat.mul_succ]
    congr 1
    omega
  have hm2 : (m - 1) * C.card + C.card = m * C.card := by
    cases m with
    | zero => omega
    | succ k => simp [Nat.succ_mul]
  omega

/-- A degree is smaller than the number of vertices. -/
lemma degree_add_one_le_card (x : V) : G.degree x + 1 ≤ Fintype.card V := by
  have hsub : G.neighborFinset x ⊆ Finset.univ.erase x := by
    intro y hy
    rw [mem_neighborFinset] at hy
    exact Finset.mem_erase.mpr ⟨hy.ne', Finset.mem_univ y⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
    G.card_neighborFinset_eq_degree] at h1
  have h2 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  omega

end Reductions

section Main

/-- **Mader (1973), Satz 1**, core form: if `G` has at least `m` vertices and no two distinct
vertices of `G` survive the deletion of some `m - 1` edges, then
`∑_x max (deg x) (m-1) ≤ m (N-1)`.  The proof is Mader's induction on `N`. -/
theorem sumMax_le_of_minCut_lt {m : ℕ} (hm : 2 ≤ m) : ∀ n : ℕ,
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → m ≤ n → (∀ x y : V, x ≠ y → minCut G x y < m) →
      ∑ x : V, max (G.degree x) (m - 1) ≤ m * (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hcard hmn hlow
  classical
  set big : Finset V := Finset.univ.filter (fun x ↦ m ≤ G.degree x) with hbigdef
  by_cases hbc : big.card ≤ 1
  · have hpt : ∀ x : V, max (G.degree x) (m - 1)
        ≤ (if m ≤ G.degree x then n - 1 else m - 1) := by
      intro x
      by_cases hx : m ≤ G.degree x
      · rw [ite_eq_left hx]
        have h := degree_add_one_le_card (G := G) x
        omega
      · rw [ite_eq_right hx]
        omega
    have hle : ∑ x : V, max (G.degree x) (m - 1)
        ≤ ∑ x : V, (if m ≤ G.degree x then n - 1 else m - 1) :=
      Finset.sum_le_sum fun x _ ↦ hpt x
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at hle
    have hcards : big.card
        + (Finset.univ.filter (fun x ↦ ¬ m ≤ G.degree x)).card = n := by
      rw [hbigdef, ← hcard, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not _
    have hb01 : big.card = 0 ∨ big.card = 1 := by omega
    have e1 : n * (m - 1) + n * 1 = n * m := by rw [← Nat.mul_add]; congr 1; omega
    have e2 : m * (n - 1) + m * 1 = m * n := by rw [← Nat.mul_add]; congr 1; omega
    have e3 : n * m = m * n := Nat.mul_comm _ _
    have e4 : (n - 1) * (m - 1) + (n - 1) * 1 = (n - 1) * m := by
      rw [← Nat.mul_add]; congr 1; omega
    have e5 : (n - 1) * m = m * (n - 1) := Nat.mul_comm _ _
    rcases hb01 with h0 | h0
    · rw [h0] at hle hcards
      simp only [Nat.zero_mul, Nat.zero_add] at hle hcards
      rw [hcards] at hle
      omega
    · rw [h0] at hle hcards
      simp only [Nat.one_mul] at hle
      have hk : (Finset.univ.filter (fun x ↦ ¬ m ≤ G.degree x)).card = n - 1 := by omega
      rw [hk] at hle
      omega
  · rw [Nat.not_le] at hbc
    obtain ⟨a₁, h1big, a₂, h2big, hne⟩ := Finset.one_lt_card.mp hbc
    have hd1 : m ≤ G.degree a₁ := by
      simpa [hbigdef] using h1big
    have hd2 : m ≤ G.degree a₂ := by
      simpa [hbigdef] using h2big
    obtain ⟨B, ha1B, ha2B, hBcut⟩ := exists_cutSize_eq_minCut (G := G) hne
    set A : Finset V := Bᶜ with hAdef
    have hBA : (Aᶜ : Finset V) = B := by rw [hAdef, compl_compl]
    have hAeq : cutSize G A = cutSize G B := cutSize_compl B
    have ha1A : a₁ ∈ A := by rw [hAdef, Finset.mem_compl]; exact ha1B
    have ha2A : a₂ ∉ A := by rw [hAdef, Finset.mem_compl]; exact fun h ↦ h ha2B
    have ht : cutSize G A < m := by rw [hAeq, hBcut]; exact hlow a₁ a₂ hne
    have htB : cutSize G B < m := by rw [← hAeq]; exact ht
    have hminA : ∀ S : Finset V, a₁ ∉ S → a₂ ∈ S → cutSize G A ≤ cutSize G S := by
      intro S hS1 hS2
      rw [hAeq, hBcut]
      exact minCut_le hS1 hS2
    have hminB : ∀ S : Finset V, a₂ ∉ S → a₁ ∈ S → cutSize G B ≤ cutSize G S := by
      intro S hS2 hS1
      rw [hBcut, minCut_comm]
      exact minCut_le hS2 hS1
    have hbdA : (boundary G A).card < m := lt_of_le_of_lt (card_boundary_le_cutSize A) ht
    have hbdB : (boundary G B).card < m := lt_of_le_of_lt (card_boundary_le_cutSize B) htB
    -- both sides have at least two vertices
    have htwo : ∀ (W : Finset V) (a : V), a ∈ W → m ≤ G.degree a → cutSize G W < m →
        2 ≤ W.card := by
      intro W a haW hda htW
      have hout : outDeg G W a ≤ cutSize G W := by
        rw [cutSize_eq_sum_outDeg]
        exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le _) haW
      have hsplit := degree_eq_inter_add_outDeg (G := G) W a
      have hpos : 0 < (G.neighborFinset a ∩ W).card := by omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_inter, mem_neighborFinset] at hy
      exact Finset.one_lt_card.mpr ⟨a, haW, y, hy.2, hy.1.ne⟩
    have hA2 : 2 ≤ A.card := htwo A a₁ ha1A hd1 ht
    have hB2 : 2 ≤ B.card := htwo B a₂ ha2B hd2 htB
    have hAB : A.card + B.card = n := by
      rw [hAdef, Finset.card_compl, hcard]
      have : B.card ≤ n := by rw [← hcard, ← Finset.card_univ]; exact Finset.card_le_univ B
      omega
    -- boundaries are strictly smaller than their sides
    have hC1 : (boundary G A).card < A.card := by
      have h := degree_add_card_boundary_le (G := G) ha1A
      omega
    have hC2 : (boundary G B).card < B.card := by
      have h := degree_add_card_boundary_le (G := G) ha2B
      omega
    -- the contraction bounds
    have hsideA : ∑ x ∈ A, max (G.degree x) (m - 1) + (boundary G A).card + (m - 1)
        ≤ m * A.card + cutSize G A := by
      refine side_bound hm ha1A hd1 ht (fun hAm ↦ ?_)
      have hcardO : Fintype.card (Option {v // v ∈ A}) = A.card + 1 := by
        rw [Fintype.card_option, Fintype.card_coe]
      have h := ih (A.card + 1) (by omega) (contract G A) hcardO hAm
        (minCut_contract_lt ha1A ha2A hminA hbdA hlow)
      simpa using h
    have hsideB : ∑ x ∈ B, max (G.degree x) (m - 1) + (boundary G B).card + (m - 1)
        ≤ m * B.card + cutSize G B := by
      refine side_bound hm ha2B hd2 htB (fun hBm ↦ ?_)
      have ha1B' : a₁ ∉ B := ha1B
      have hcardO : Fintype.card (Option {v // v ∈ B}) = B.card + 1 := by
        rw [Fintype.card_option, Fintype.card_coe]
      have h := ih (B.card + 1) (by omega) (contract G B) hcardO hBm
        (minCut_contract_lt ha2B ha1B' hminB hbdB hlow)
      simpa using h
    -- the deletion bounds
    have hdelA : ∑ x ∈ B, max (G.degree x) (m - 1) + m
        ≤ (boundary G A).card + m * B.card := by
      have hkey : ∑ x ∈ (Aᶜ : Finset V), max (G.degree x) (m - 1) + m
          ≤ (boundary G A).card + m * (Aᶜ : Finset V).card := by
        refine del_bound hm (by rw [hBA]; exact Finset.card_pos.mp (by omega)) ?_
        set D : Finset V := boundary G A ∪ Aᶜ with hDdef
        have hdisj : Disjoint (boundary G A) (Aᶜ : Finset V) := by
          rw [Finset.disjoint_right]
          intro x hx hxC
          exact (Finset.mem_compl.mp hx) (boundary_subset A hxC)
        have hDcard : D.card = (boundary G A).card + (Aᶜ : Finset V).card :=
          Finset.card_union_of_disjoint hdisj
        rw [hBA] at hDcard
        have hsubD : insert a₂ (G.neighborFinset a₂) ⊆ D := by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_union_right _ (by rw [hBA]; exact ha2B)
          · rw [mem_neighborFinset] at hy
            by_cases hyA : y ∈ A
            · refine Finset.mem_union_left _ ?_
              rw [mem_boundary]
              refine ⟨hyA, ?_⟩
              rw [outDeg, Finset.card_pos]
              refine ⟨a₂, Finset.mem_sdiff.mpr ⟨?_, ha2A⟩⟩
              rw [mem_neighborFinset]
              exact hy.symm
            · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hyA)
        have hcardD : m ≤ D.card := by
          have h1 := Finset.card_le_card hsubD
          rw [Finset.card_insert_of_notMem (by simp [mem_neighborFinset]),
            G.card_neighborFinset_eq_degree] at h1
          omega
        have h := ih D.card (by omega) (sub G D) (Fintype.card_coe D) hcardD
          (minCut_sub_lt hlow)
        exact h
      rwa [hBA] at hkey
    have hdelB : ∑ x ∈ A, max (G.degree x) (m - 1) + m
        ≤ (boundary G B).card + m * A.card := by
      have hAB' : (Bᶜ : Finset V) = A := hAdef.symm
      have hkey : ∑ x ∈ (Bᶜ : Finset V), max (G.degree x) (m - 1) + m
          ≤ (boundary G B).card + m * (Bᶜ : Finset V).card := by
        refine del_bound hm (by rw [hAB']; exact Finset.card_pos.mp (by omega)) ?_
        set D : Finset V := boundary G B ∪ Bᶜ with hDdef
        have hdisj : Disjoint (boundary G B) (Bᶜ : Finset V) := by
          rw [Finset.disjoint_right]
          intro x hx hxC
          exact (Finset.mem_compl.mp hx) (boundary_subset B hxC)
        have hDcard : D.card = (boundary G B).card + (Bᶜ : Finset V).card :=
          Finset.card_union_of_disjoint hdisj
        rw [hAB'] at hDcard
        have hsubD : insert a₁ (G.neighborFinset a₁) ⊆ D := by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_union_right _ (by rw [hAB']; exact ha1A)
          · rw [mem_neighborFinset] at hy
            by_cases hyB : y ∈ B
            · refine Finset.mem_union_left _ ?_
              rw [mem_boundary]
              refine ⟨hyB, ?_⟩
              rw [outDeg, Finset.card_pos]
              refine ⟨a₁, Finset.mem_sdiff.mpr ⟨?_, ha1B⟩⟩
              rw [mem_neighborFinset]
              exact hy.symm
            · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hyB)
        have hcardD : m ≤ D.card := by
          have h1 := Finset.card_le_card hsubD
          rw [Finset.card_insert_of_notMem (by simp [mem_neighborFinset]),
            G.card_neighborFinset_eq_degree] at h1
          omega
        have h := ih D.card (by omega) (sub G D) (Fintype.card_coe D) hcardD
          (minCut_sub_lt hlow)
        exact h
      rwa [hAB'] at hkey
    have hsplit : ∑ x ∈ A, max (G.degree x) (m - 1) + ∑ x ∈ B, max (G.degree x) (m - 1)
        = ∑ x : V, max (G.degree x) (m - 1) := by
      rw [← hBA]
      exact Finset.sum_add_sum_compl A _
    have p1 : m * A.card + m * B.card = m * n := by rw [← Nat.mul_add, hAB]
    have p2 : m * (n - 1) + m * 1 = m * n := by rw [← Nat.mul_add]; congr 1; omega
    omega

/-- **Mader (1973), Satz 1**, in the clean form `∑_x max (deg x) (m-1) > m (N-1)`. -/
theorem hasEdgeRails_of_lt_sumMax {m : ℕ} (hm : 2 ≤ m) {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hN : m ≤ Fintype.card V)
    (h : m * (Fintype.card V - 1) < ∑ x : V, max (G.degree x) (m - 1)) :
    HasEdgeRails G m := by
  classical
  by_contra hcon
  have hlow : ∀ x y : V, x ≠ y → minCut G x y < m := by
    intro x y hxy
    by_contra hle
    rw [Nat.not_lt] at hle
    exact hcon ((hasEdgeRails_iff_exists_isEdgeReachable m).mpr
      ⟨x, y, hxy, isEdgeReachable_of_le_minCut hle⟩)
  have hkey := sumMax_le_of_minCut_lt hm (Fintype.card V) G rfl hN hlow
  omega

/-- **Mader (1973), Satz 1.**  A finite simple graph on `N ≥ m` vertices with
`m (N - 1) < 2|E| + e_0 + ⋯ + e_{m-2}` has two vertices joined by `m` edge-disjoint paths. -/
theorem mader_edge_rails {m : ℕ} (hm : 2 ≤ m) {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hN : m ≤ Fintype.card V)
    (h : m * (Fintype.card V - 1) <
      2 * G.edgeSet.ncard + ∑ r ∈ Finset.range (m - 1), lowDegreeCount G r) :
    HasEdgeRails G m := by
  refine hasEdgeRails_of_lt_sumMax hm G hN ?_
  rwa [sumMax_eq_two_mul_card_edges_add_sigma]

end Main

end Erdos915

