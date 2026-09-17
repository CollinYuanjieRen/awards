import Proof.Defs

/-!
# Erdős problem #1017 — the Erdős–Goodman–Pósa bound `n²/4` is sharp

The problem page records that the Erdős–Goodman–Pósa bound `f(n, k) ≤ n²/4` "is best possible in
general, as witnessed for example by a complete bipartite graph".  This file proves that remark: the
balanced complete bipartite graph on `n` vertices is triangle-free (T6) with `⌊n²/4⌋` edges (T3), a
triangle-free graph needs exactly as many complete graphs as it has edges (T4, with the trivial
bound T5), so the witness has clique partition number `⌊n²/4⌋` (T2) and `⌊n²/4⌋ ≤ f(n, ⌊n²/4⌋)`
(T1, the audited root).

Not claimed here: the Erdős–Goodman–Pósa upper bound `f(n, k) ≤ n²/4` itself, its refinement that
the complete graphs can be taken to be edges and triangles, Lovász's covering theorem, and the
question of the problem page for `k > n²/4`.
-/

namespace Erdos1017

open SimpleGraph

/-! ### Basic facts about `edgesOf` -/

/-- Membership in `edgesOf T`: the off-diagonal pairs with both endpoints in `T`. -/
theorem mem_edgesOf {V : Type*} [DecidableEq V] {T : Finset V} {e : Sym2 V} :
    e ∈ edgesOf T ↔ (∀ x ∈ e, x ∈ T) ∧ ¬ e.IsDiag := by
  simp [edgesOf, Finset.mem_filter, Finset.mem_sym2_iff]

/-- An unordered pair is determined by the finset of its endpoints. -/
theorem sym2_eq_of_toFinset_eq {V : Type*} [DecidableEq V] {e e' : Sym2 V}
    (h : e.toFinset = e'.toFinset) : e = e' :=
  Sym2.ext fun x => by rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, h]

/-- An edge of a two-element part spans exactly that part. -/
theorem toFinset_eq_of_mem_edgesOf {V : Type*} [DecidableEq V] {T : Finset V} {e : Sym2 V}
    (he : e ∈ edgesOf T) (hT : T.card ≤ 2) : e.toFinset = T := by
  obtain ⟨hmem, hdiag⟩ := mem_edgesOf.1 he
  have hsub : e.toFinset ⊆ T := fun x hx => hmem x (Sym2.mem_toFinset.1 hx)
  have hcard : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e hdiag
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-! ### T5: the edges themselves form a clique partition -/

/-- The finsets of endpoints of the edges of `G` form a clique partition of `G`. -/
theorem isCliquePartition_image_toFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet] :
    IsCliquePartition G (G.edgeFinset.image Sym2.toFinset) := by
  constructor
  · intro S hS
    simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset] at hS
    obtain ⟨e, he, rfl⟩ := hS
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := he
      constructor
      · rw [Sym2.toFinset_mk_eq]
        simpa using SimpleGraph.isClique_pair.2 fun _ => hab
      · rw [Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet he)]
  · intro e he
    refine ⟨e.toFinset, ⟨Finset.mem_image_of_mem _ (SimpleGraph.mem_edgeFinset.2 he), ?_⟩, ?_⟩
    · exact mem_edgesOf.2 ⟨fun x hx => Sym2.mem_toFinset.2 hx, G.not_isDiag_of_mem_edgeSet he⟩
    · rintro S ⟨hSP, hSe⟩
      simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset] at hSP
      obtain ⟨e', he', rfl⟩ := hSP
      exact (toFinset_eq_of_mem_edgesOf hSe
        (le_of_eq (Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet he')))).symm

/-- The set whose infimum defines `cliquePartitionNum` is nonempty. -/
theorem cliquePartitionNum_mem_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet] :
    {m : ℕ | ∃ P : Finset (Finset V), IsCliquePartition G P ∧ P.card = m}.Nonempty :=
  ⟨_, ⟨_, isCliquePartition_image_toFinset G, rfl⟩⟩

/-- Auxiliary form of (T5) depending only on a `Fintype` structure on the edge set. -/
theorem cliquePartitionNum_le_card_edgeFinset' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet] : cliquePartitionNum G ≤ G.edgeFinset.card :=
  le_trans (Nat.sInf_le ⟨_, isCliquePartition_image_toFinset G, rfl⟩) (Finset.card_image_le)

/-- (T5) The edges of `G` form a clique partition, so `cliquePartitionNum G ≤ |E(G)|`. -/
theorem cliquePartitionNum_le_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : cliquePartitionNum G ≤ G.edgeFinset.card :=
  cliquePartitionNum_le_card_edgeFinset' G

/-! ### T4: in a triangle-free graph the parts are single edges -/

/-- A clique in a triangle-free graph has at most two vertices. -/
theorem card_le_two_of_cliqueFree {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (h : G.CliqueFree 3) {S : Finset V} (hS : G.IsClique (S : Set V)) : S.card ≤ 2 := by
  by_contra hlt
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
  exact h t ⟨hS.subset (by exact_mod_cast hts), htc⟩

/-- (T4) In a triangle-free graph every clique partition consists of single edges, so the clique
partition number is the number of edges. -/
theorem cliquePartitionNum_eq_of_cliqueFree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) : cliquePartitionNum G = G.edgeFinset.card := by
  refine le_antisymm (cliquePartitionNum_le_card_edgeFinset G) ?_
  refine le_csInf (cliquePartitionNum_mem_nonempty G) ?_
  rintro m ⟨P, hP, rfl⟩
  classical
  set F : Sym2 V → Finset V := fun e =>
    if he : e ∈ G.edgeSet then (hP.2 e he).choose else ∅ with hF
  have hFmem : ∀ e ∈ G.edgeSet, F e ∈ P ∧ e ∈ edgesOf (F e) := by
    intro e he
    simpa [hF, he] using (hP.2 e he).choose_spec.1
  refine Finset.card_le_card_of_injOn F ?_ ?_
  · intro e he
    exact (hFmem e (SimpleGraph.mem_edgeFinset.1 he)).1
  · intro e₁ h₁ e₂ h₂ heq
    have h₁' := hFmem e₁ (SimpleGraph.mem_edgeFinset.1 h₁)
    have h₂' := hFmem e₂ (SimpleGraph.mem_edgeFinset.1 h₂)
    have hcard : (F e₁).card ≤ 2 := card_le_two_of_cliqueFree h (hP.1 _ h₁'.1).1
    refine sym2_eq_of_toFinset_eq ?_
    rw [toFinset_eq_of_mem_edgesOf h₁'.2 hcard, heq,
      toFinset_eq_of_mem_edgesOf h₂'.2 (heq ▸ hcard)]

/-! ### T6: the balanced complete bipartite graph is triangle-free -/

/-- (T6) The balanced complete bipartite graph is triangle-free. -/
theorem balancedBipartite_cliqueFree_three (n : ℕ) : (balancedBipartite n).CliqueFree 3 := by
  intro t ht
  have hc : t.card = 3 := ht.card_eq
  have key : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → (balancedBipartite n).Adj x y := by
    intro x hx y hy hxy
    exact ht.isClique (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hxy
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := t) (p := fun i : Fin n => i.val < n / 2)
  have hcase : 2 ≤ (t.filter (fun i : Fin n => i.val < n / 2)).card ∨
      2 ≤ (t.filter (fun i : Fin n => ¬ i.val < n / 2)).card := by omega
  rcases hcase with h2 | h2
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1
      (show 1 < (t.filter (fun i : Fin n => i.val < n / 2)).card by omega)
    rw [Finset.mem_filter] at hx hy
    have hadj := key x hx.1 y hy.1 hxy
    rw [balancedBipartite, SimpleGraph.fromRel_adj] at hadj
    have hx2 := hx.2
    have hy2 := hy.2
    omega
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1
      (show 1 < (t.filter (fun i : Fin n => ¬ i.val < n / 2)).card by omega)
    rw [Finset.mem_filter] at hx hy
    have hadj := key x hx.1 y hy.1 hxy
    rw [balancedBipartite, SimpleGraph.fromRel_adj] at hadj
    have hx2 := hx.2
    have hy2 := hy.2
    omega

/-! ### T3: the balanced complete bipartite graph has `⌊n²/4⌋` edges -/

/-- Counting the elements of `Fin n` below a threshold `k ≤ n`. -/
theorem card_univ_filter_val_lt (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have himg : (Finset.univ.filter (fun i : Fin n => i.val < k)).image Fin.val
      = Finset.range k := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx; exact ⟨⟨x, lt_of_lt_of_le hx hk⟩, hx, rfl⟩
  have hinj := Finset.card_image_of_injective
    (Finset.univ.filter (fun i : Fin n => i.val < k)) Fin.val_injective
  rw [himg, Finset.card_range] at hinj
  exact hinj.symm

/-- Counting the elements of `Fin n` at or above a threshold `k ≤ n`. -/
theorem card_univ_filter_le_val (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i.val)).card = n - k := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => i.val < k)
  have hlt := card_univ_filter_val_lt n k hk
  have hne : (Finset.univ.filter (fun i : Fin n => ¬ i.val < k)).card
      = (Finset.univ.filter (fun i : Fin n => k ≤ i.val)).card := by
    exact congrArg Finset.card (Finset.filter_congr (fun i _ => by omega))
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- The degree of a vertex in the balanced complete bipartite graph. -/
theorem degree_balancedBipartite (n : ℕ) (i : Fin n) :
    (balancedBipartite n).degree i = if i.val < n / 2 then n - n / 2 else n / 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  split_ifs with hi
  · have : (Finset.univ.filter ((balancedBipartite n).Adj i))
        = Finset.univ.filter (fun j : Fin n => n / 2 ≤ j.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [balancedBipartite, SimpleGraph.fromRel_adj]
      simp only [ne_eq, Fin.ext_iff]
      omega
    rw [this, card_univ_filter_le_val n (n / 2) (Nat.div_le_self n 2)]
  · have : (Finset.univ.filter ((balancedBipartite n).Adj i))
        = Finset.univ.filter (fun j : Fin n => j.val < n / 2) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [balancedBipartite, SimpleGraph.fromRel_adj]
      simp only [ne_eq, Fin.ext_iff]
      omega
    rw [this, card_univ_filter_val_lt n (n / 2) (Nat.div_le_self n 2)]

/-- `⌊n²/4⌋ = ⌊n/2⌋ · ⌈n/2⌉`. -/
theorem sq_div_four (n : ℕ) : n ^ 2 / 4 = n / 2 * (n - n / 2) := by
  have e4 : ∀ p : ℕ, (4 * p + 1) / 4 = p := by intro p; omega
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e1 : (2 * m) ^ 2 = 4 * (m * m) := by ring
    have e2 : 2 * m / 2 = m := by omega
    have e3 : 2 * m - m = m := by omega
    rw [e1, e2, e3, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  · have e1 : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
    have e2 : (2 * m + 1) / 2 = m := by omega
    have e3 : 2 * m + 1 - m = m + 1 := by omega
    rw [e1, e2, e3, e4]
    ring

/-- (T3) The balanced complete bipartite graph on `n` vertices has `⌊n²/4⌋` edges. -/
theorem card_edgeFinset_balancedBipartite (n : ℕ) : (balancedBipartite n).edgeFinset.card = n ^ 2 / 4 := by
  have hsum := (balancedBipartite n).sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => degree_balancedBipartite n i),
    Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
    card_univ_filter_val_lt n (n / 2) (Nat.div_le_self n 2)] at hsum
  rw [show (Finset.univ.filter (fun i : Fin n => ¬ i.val < n / 2))
      = Finset.univ.filter (fun i : Fin n => n / 2 ≤ i.val) from
    Finset.filter_congr (fun i _ => by omega),
    card_univ_filter_le_val n (n / 2) (Nat.div_le_self n 2)] at hsum
  rw [sq_div_four n]
  have hcomm : (n - n / 2) * (n / 2) = n / 2 * (n - n / 2) := Nat.mul_comm _ _
  omega

/-! ### T2 and T1 -/

/-- The number of edges does not depend on the chosen `Fintype` structure on the edge set. -/
theorem card_edgeFinset_congr {V : Type*} (G : SimpleGraph V) (i₁ i₂ : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset V G i₁).card = (@SimpleGraph.edgeFinset V G i₂).card := by
  rw [Subsingleton.elim i₁ i₂]

/-- (T2) The balanced complete bipartite graph needs `⌊n²/4⌋` edge-disjoint complete graphs. -/
theorem cliquePartitionNum_balancedBipartite (n : ℕ) : cliquePartitionNum (balancedBipartite n) = n ^ 2 / 4 := by
  rw [cliquePartitionNum_eq_of_cliqueFree _ (balancedBipartite_cliqueFree_three n),
    card_edgeFinset_balancedBipartite n]

/-- (T1) Audited root: the Erdős–Goodman–Pósa bound `f(n, k) ≤ n²/4` is best possible, as the
balanced complete bipartite graph shows: `⌊n²/4⌋ ≤ f(n, ⌊n²/4⌋)`. -/
theorem sq_div_four_le_f (n : ℕ) : n ^ 2 / 4 ≤ f n (n ^ 2 / 4) := by
  classical
  unfold f
  refine le_csSup ⟨n ^ 2 / 4, ?_⟩ ?_
  · rintro m ⟨G, hG, rfl⟩
    refine le_trans (cliquePartitionNum_le_card_edgeFinset' G) ?_
    rw [← hG]
  · refine ⟨balancedBipartite n, ?_, cliquePartitionNum_balancedBipartite n⟩
    rw [← card_edgeFinset_balancedBipartite n]
    exact card_edgeFinset_congr _ _ _

end Erdos1017
