import Mathlib

/-!
# Erdős problem #629: the Erdős–Rubin–Taylor lower bound for `n(k)`

Let `n(k)` be the least number of vertices of a bipartite graph `G` with list chromatic number
`χ_L(G) > k`.  Erdős, Rubin and Taylor (1979) proved `2^{k-1} < n(k)`.

This file develops list colourings from scratch (`Erdos629.ListColorable`, `Erdos629.Choosable`,
`Erdos629.listThreshold`) and proves:

* `Erdos629.choosable_of_card_lt`: every `2`-colourable graph on fewer than `2 ^ k` vertices is
  `k`-choosable (the random/double-counting argument of Erdős–Rubin–Taylor);
* `Erdos629.exists_bipartite_not_choosable`: for every `k` there is a bipartite graph that is not
  `k`-choosable, namely `K_{m,m}` with `m = C(2k-1, k)` for `k ≥ 1`;
* `Erdos629.two_pow_le_listThreshold`: `2 ^ k ≤ n(k)`;
* `Erdos629.ert_lower_bound`: `2 ^ (k - 1) < n(k)` for `k ≥ 1` (the form stated on the problem page);
* `Erdos629.listThreshold_le`: `n(k) ≤ 2 * C(2k-1, k)`;
* `Erdos629.listThreshold_one`: `n(1) = 2`.
-/

namespace Erdos629

/-! ## Definitions -/

/-- A list assignment `L` with lists of size `k` admits a proper colouring from the lists. -/
def ListColorable {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ) : Prop :=
  ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- `G` is `k`-choosable: every assignment of lists of size `k` (colours are natural numbers)
admits a proper list colouring. -/
def Choosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ListColorable G L

/-- `n(k)`: the least number of vertices of a bipartite graph (a `2`-colourable graph on `Fin n`)
that is not `k`-choosable. -/
noncomputable def listThreshold (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.Colorable 2 ∧ ¬ Choosable G k}

/-- Choosability transports along an equivalence of vertex types: if the graph pulled back along
`e` is `k`-choosable then so is the original graph. -/
theorem choosable_comap {V W : Type*} (e : V ≃ W) (G : SimpleGraph W) (k : ℕ)
    (h : Choosable (G.comap e) k) : Choosable G k := by
  intro L hL
  obtain ⟨c, hc1, hc2⟩ := h (fun v => L (e v)) (fun v => hL (e v))
  refine ⟨fun w => c (e.symm w), fun w => ?_, fun u v huv => ?_⟩
  · simpa using hc1 (e.symm w)
  · refine hc2 _ _ ?_
    show G.Adj (e (e.symm u)) (e (e.symm v))
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ## Part 1: every bipartite graph on fewer than `2 ^ k` vertices is `k`-choosable -/

/-- Given a `2`-colouring `c`, a list assignment `L` and a set `S` of colours, the *bad* vertices
for `S` are those in the class `c v = 0` whose list misses `S` entirely, together with those in the
class `c v ≠ 0` whose list is contained in `S`. -/
noncomputable def badSet {V : Type*} [Fintype V] (c : V → Fin 2) (L : V → Finset ℕ)
    (S : Finset ℕ) : Finset V :=
  @Finset.filter V (fun v => if c v = 0 then Disjoint (L v) S else L v ⊆ S)
    (Classical.decPred _) Finset.univ

/-- Membership in `badSet` for a vertex of the first colour class. -/
theorem mem_badSet_zero {V : Type*} [Fintype V] {c : V → Fin 2} {L : V → Finset ℕ}
    {S : Finset ℕ} {v : V} (h : c v = 0) : v ∈ badSet c L S ↔ Disjoint S (L v) := by
  have h1 : v ∈ badSet c L S ↔ Disjoint (L v) S := by
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, h]
    simp
  rw [h1]
  exact disjoint_comm

/-- Membership in `badSet` for a vertex of the second colour class. -/
theorem mem_badSet_one {V : Type*} [Fintype V] {c : V → Fin 2} {L : V → Finset ℕ}
    {S : Finset ℕ} {v : V} (h : c v ≠ 0) : v ∈ badSet c L S ↔ L v ⊆ S := by
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, h]
  simp

/-- **Erdős–Rubin–Taylor, universal bound.** Every `2`-colourable (i.e. bipartite) graph on fewer
than `2 ^ k` vertices is `k`-choosable. -/
theorem choosable_of_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Colorable 2)
    (k : ℕ) (hV : Fintype.card V < 2 ^ k) : Choosable G k := by
  classical
  intro L hL
  obtain ⟨c⟩ := hG
  rcases isEmpty_or_nonempty V with hemp | hne
  · exact ⟨fun v => (hemp.false v).elim, fun v => (hemp.false v).elim,
      fun u _ _ => (hemp.false u).elim⟩
  obtain ⟨v₀⟩ := hne
  set C : Finset ℕ := Finset.univ.biUnion L with hCdef
  have hLC : ∀ v, L v ⊆ C := fun v => Finset.subset_biUnion_of_mem L (Finset.mem_univ v)
  have hkC : k ≤ C.card := by
    rw [← hL v₀]
    exact Finset.card_le_card (hLC v₀)
  have hvertex : ∀ v : V,
      (∑ S ∈ C.powerset, (if v ∈ badSet c L S then 1 else 0)) = 2 ^ (C.card - k) := by
    intro v
    rw [← Finset.card_filter]
    by_cases h : c v = 0
    · have hEq : {S ∈ C.powerset | v ∈ badSet c L S} = (C \ L v).powerset := by
        ext S
        simp [mem_badSet_zero h, Finset.subset_sdiff]
      rw [hEq, Finset.card_powerset, Finset.card_sdiff_of_subset (hLC v), hL v]
    · have hEq : {S ∈ C.powerset | v ∈ badSet c L S} = Finset.Icc (L v) C := by
        ext S
        simp [mem_badSet_one h, Finset.mem_Icc, and_comm]
      rw [hEq, Finset.card_Icc_finset (hLC v), hL v]
  have hcard : ∀ B : Finset V, B.card = ∑ v : V, (if v ∈ B then 1 else 0) := by
    intro B
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]
  have htot : (∑ S ∈ C.powerset, (badSet c L S).card) < C.powerset.card := by
    calc (∑ S ∈ C.powerset, (badSet c L S).card)
        = ∑ S ∈ C.powerset, ∑ v : V, (if v ∈ badSet c L S then 1 else 0) :=
          Finset.sum_congr rfl fun S _ => hcard _
      _ = ∑ v : V, ∑ S ∈ C.powerset, (if v ∈ badSet c L S then 1 else 0) := Finset.sum_comm
      _ = ∑ _v : V, 2 ^ (C.card - k) := Finset.sum_congr rfl fun v _ => hvertex v
      _ = Fintype.card V * 2 ^ (C.card - k) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
      _ < 2 ^ k * 2 ^ (C.card - k) := mul_lt_mul_of_pos_right hV (Nat.two_pow_pos _)
      _ = 2 ^ C.card := by rw [← pow_add, Nat.add_sub_cancel' hkC]
      _ = C.powerset.card := (Finset.card_powerset C).symm
  obtain ⟨S, -, hS0⟩ : ∃ S ∈ C.powerset, (badSet c L S).card = 0 := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hge : C.powerset.card ≤ ∑ S ∈ C.powerset, (badSet c L S).card := by
      calc C.powerset.card = ∑ _S ∈ C.powerset, 1 := Finset.card_eq_sum_ones _
        _ ≤ _ := Finset.sum_le_sum fun S hS => Nat.one_le_iff_ne_zero.mpr (hcon S hS)
    omega
  have hSempty : ∀ v, v ∉ badSet c L S := by
    rw [Finset.card_eq_zero] at hS0
    intro v hv
    rw [hS0] at hv
    simp at hv
  have hex : ∀ v : V, ∃ a, a ∈ L v ∧ (c v = 0 ↔ a ∈ S) := by
    intro v
    by_cases h : c v = 0
    · have hb := hSempty v
      rw [mem_badSet_zero h] at hb
      obtain ⟨a, ha1, ha2⟩ := Finset.not_disjoint_iff.mp hb
      exact ⟨a, ha2, iff_of_true h ha1⟩
    · have hb := hSempty v
      rw [mem_badSet_one h] at hb
      obtain ⟨a, ha1, ha2⟩ := Finset.not_subset.mp hb
      exact ⟨a, ha1, iff_of_false h ha2⟩
  choose col hcol1 hcol2 using hex
  have h2 : ∀ x y : Fin 2, (x = 0 ↔ y = 0) → x = y := by decide
  refine ⟨col, hcol1, fun u v huv hcuv => ?_⟩
  exact c.valid huv (h2 _ _ (by rw [hcol2 u, hcol2 v, hcuv]))

/-! ## Part 2: the Erdős–Rubin–Taylor witness `K_{m,m}`, `m = C(2k-1, k)` -/

/-- `m k = C(2k-1, k)`, the number of `k`-element subsets of `{0, …, 2k-2}`. -/
def mK (k : ℕ) : ℕ := (2 * k - 1).choose k

/-- There are exactly `m k` subsets of size `k` of `Finset.range (2 * k - 1)`. -/
theorem card_kSubsets (k : ℕ) :
    ((Finset.range (2 * k - 1)).powersetCard k).card = mK k := by
  rw [Finset.card_powersetCard, Finset.card_range]
  rfl

/-- An enumeration of the `k`-element subsets of `{0, …, 2k-2}` by `Fin (m k)`. -/
noncomputable def kSubsetEquiv (k : ℕ) :
    Fin (mK k) ≃ ↥((Finset.range (2 * k - 1)).powersetCard k) :=
  (Finset.equivFinOfCardEq (card_kSubsets k)).symm

/-- The `i`-th `k`-element subset of `{0, …, 2k-2}`. -/
noncomputable def kSubset (k : ℕ) (i : Fin (mK k)) : Finset ℕ := (kSubsetEquiv k i).1

/-- `kSubset k i` is one of the `k`-element subsets of `Finset.range (2 * k - 1)`. -/
theorem kSubset_mem (k : ℕ) (i : Fin (mK k)) :
    kSubset k i ∈ (Finset.range (2 * k - 1)).powersetCard k := (kSubsetEquiv k i).2

/-- Each list `kSubset k i` has exactly `k` colours. -/
theorem kSubset_card (k : ℕ) (i : Fin (mK k)) : (kSubset k i).card = k :=
  (Finset.mem_powersetCard.mp (kSubset_mem k i)).2

/-- Each list `kSubset k i` uses only colours `< 2 * k - 1`. -/
theorem kSubset_subset (k : ℕ) (i : Fin (mK k)) : kSubset k i ⊆ Finset.range (2 * k - 1) :=
  (Finset.mem_powersetCard.mp (kSubset_mem k i)).1

/-- Every `k`-element subset of `{0, …, 2k-2}` occurs as some list `kSubset k i`. -/
theorem kSubset_surj (k : ℕ) {T : Finset ℕ} (h1 : T ⊆ Finset.range (2 * k - 1))
    (h2 : T.card = k) : ∃ i, kSubset k i = T := by
  refine ⟨(kSubsetEquiv k).symm ⟨T, Finset.mem_powersetCard.mpr ⟨h1, h2⟩⟩, ?_⟩
  simp [kSubset]

/-- The Erdős–Rubin–Taylor list assignment on `K_{m,m}`: both sides receive all `k`-element
subsets of `{0, …, 2k-2}`, each exactly once. -/
noncomputable def witnessList (k : ℕ) : Fin (mK k) ⊕ Fin (mK k) → Finset ℕ :=
  Sum.elim (kSubset k) (kSubset k)

/-- The canonical `2`-colouring of a complete bipartite graph. -/
def bipartiteColoring (m n : ℕ) : (completeBipartiteGraph (Fin m) (Fin n)).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) (by
    intro u v h
    rcases u with u | u <;> rcases v with v | v
    · simp at h
    · exact (by decide : (0 : Fin 2) ≠ 1)
    · exact (by decide : (1 : Fin 2) ≠ 0)
    · simp at h)

/-- **The Erdős–Rubin–Taylor witness.** For `k ≥ 1` the complete bipartite graph `K_{m,m}` with
`m = C(2k-1, k)` is not `k`-choosable. -/
theorem completeBipartite_not_choosable (k : ℕ) (hk : 1 ≤ k) :
    ¬ Choosable (completeBipartiteGraph (Fin (mK k)) (Fin (mK k))) k := by
  classical
  intro hch
  obtain ⟨col, hmem, hadj⟩ := hch (witnessList k) (by
    intro v
    rcases v with i | j
    · exact kSubset_card k i
    · exact kSubset_card k j)
  set CA : Finset ℕ := Finset.univ.image (fun i : Fin (mK k) => col (Sum.inl i)) with hCA
  set CB : Finset ℕ := Finset.univ.image (fun j : Fin (mK k) => col (Sum.inr j)) with hCB
  have hcross : ∀ i j : Fin (mK k), col (Sum.inl i) ≠ col (Sum.inr j) := by
    intro i j
    exact hadj _ _ (by simp)
  have hCAsub : CA ⊆ Finset.range (2 * k - 1) := by
    intro x hx
    rw [hCA, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact kSubset_subset k i (hmem (Sum.inl i))
  have hCBsub : CB ⊆ Finset.range (2 * k - 1) := by
    intro x hx
    rw [hCB, Finset.mem_image] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact kSubset_subset k j (hmem (Sum.inr j))
  have hdisj : Disjoint CA CB := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [hCA, Finset.mem_image] at hxA
    rw [hCB, Finset.mem_image] at hxB
    obtain ⟨i, -, rfl⟩ := hxA
    obtain ⟨j, -, hj⟩ := hxB
    exact hcross i j hj.symm
  have hkCA : k ≤ CA.card := by
    by_contra hlt
    have hcs : k ≤ (Finset.range (2 * k - 1) \ CA).card := by
      rw [Finset.card_sdiff_of_subset hCAsub, Finset.card_range]
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcs
    obtain ⟨i, hi⟩ := kSubset_surj k (hTsub.trans Finset.sdiff_subset) hTcard
    have h0 : col (Sum.inl i) ∈ kSubset k i := hmem (Sum.inl i)
    rw [hi] at h0
    have h3 := hTsub h0
    rw [Finset.mem_sdiff] at h3
    exact h3.2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hkCB : k ≤ CB.card := by
    by_contra hlt
    have hcs : k ≤ (Finset.range (2 * k - 1) \ CB).card := by
      rw [Finset.card_sdiff_of_subset hCBsub, Finset.card_range]
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcs
    obtain ⟨j, hj⟩ := kSubset_surj k (hTsub.trans Finset.sdiff_subset) hTcard
    have h0 : col (Sum.inr j) ∈ kSubset k j := hmem (Sum.inr j)
    rw [hj] at h0
    have h3 := hTsub h0
    rw [Finset.mem_sdiff] at h3
    exact h3.2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hun : (CA ∪ CB).card ≤ 2 * k - 1 := by
    calc (CA ∪ CB).card ≤ (Finset.range (2 * k - 1)).card :=
          Finset.card_le_card (Finset.union_subset hCAsub hCBsub)
      _ = 2 * k - 1 := Finset.card_range _
  rw [Finset.card_union_of_disjoint hdisj] at hun
  omega

/-- The Erdős–Rubin–Taylor witness transported to the vertex type `Fin (m k + m k)`. -/
def witnessGraph (k : ℕ) : SimpleGraph (Fin (mK k + mK k)) :=
  (completeBipartiteGraph (Fin (mK k)) (Fin (mK k))).comap finSumFinEquiv.symm

/-- The witness graph is bipartite, i.e. `2`-colourable. -/
theorem witnessGraph_colorable (k : ℕ) : (witnessGraph k).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun v => bipartiteColoring (mK k) (mK k) (finSumFinEquiv.symm v))
    (fun {_ _} h => (bipartiteColoring (mK k) (mK k)).valid h)⟩

/-- The witness graph is not `k`-choosable (for `k ≥ 1`). -/
theorem witnessGraph_not_choosable (k : ℕ) (hk : 1 ≤ k) : ¬ Choosable (witnessGraph k) k :=
  fun h => completeBipartite_not_choosable k hk
    (choosable_comap finSumFinEquiv.symm _ k h)

/-- The empty graph on one vertex is bipartite. -/
theorem bot_colorable : (⊥ : SimpleGraph (Fin 1)).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun {_ _} h => absurd h (by simp))⟩

/-- No graph with a vertex is `0`-choosable: the lists are empty. -/
theorem bot_not_choosable_zero : ¬ Choosable (⊥ : SimpleGraph (Fin 1)) 0 := by
  intro hch
  obtain ⟨col, hmem, -⟩ := hch (fun _ => (∅ : Finset ℕ)) (fun _ => Finset.card_empty)
  have := hmem 0
  simp at this

/-- For every `k` there is a bipartite graph that is not `k`-choosable. -/
theorem exists_bipartite_not_choosable (k : ℕ) :
    ∃ n, ∃ G : SimpleGraph (Fin n), G.Colorable 2 ∧ ¬ Choosable G k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, ⊥, bot_colorable, bot_not_choosable_zero⟩
  · exact ⟨mK k + mK k, witnessGraph k, witnessGraph_colorable k,
      witnessGraph_not_choosable k hk⟩

/-! ## Part 3: the lower bound on `n(k)` -/

/-- The minimum `n(k)` is attained: there is a bipartite graph on `n(k)` vertices that is not
`k`-choosable. -/
theorem listThreshold_mem (k : ℕ) :
    ∃ G : SimpleGraph (Fin (listThreshold k)), G.Colorable 2 ∧ ¬ Choosable G k :=
  Nat.sInf_mem (exists_bipartite_not_choosable k)

/-- **Erdős–Rubin–Taylor lower bound (sharp form).** `2 ^ k ≤ n(k)`. -/
theorem two_pow_le_listThreshold (k : ℕ) : 2 ^ k ≤ listThreshold k := by
  by_contra hcon
  simp only [Nat.not_le] at hcon
  obtain ⟨G, hGc, hGn⟩ := listThreshold_mem k
  exact hGn (choosable_of_card_lt G hGc k (by simpa using hcon))

/-- **Erdős–Rubin–Taylor lower bound**, in the form stated on the problem page:
`2 ^ (k - 1) < n(k)` for `k ≥ 1`. -/
theorem ert_lower_bound : ∀ k, 1 ≤ k → 2 ^ (k - 1) < listThreshold k := by
  intro k hk
  have h1 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact lt_of_lt_of_le h1 (two_pow_le_listThreshold k)

/-- The Erdős–Rubin–Taylor witness gives `n(k) ≤ 2 * C(2k-1, k)`. -/
theorem listThreshold_le : ∀ k, listThreshold k ≤ 2 * (2 * k - 1).choose k := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : listThreshold 0 ≤ 1 :=
      Nat.sInf_le ⟨⊥, bot_colorable, bot_not_choosable_zero⟩
    have h2 : (2 * 0 - 1).choose 0 = 1 := rfl
    omega
  · have h1 : listThreshold k ≤ mK k + mK k :=
      Nat.sInf_le ⟨witnessGraph k, witnessGraph_colorable k, witnessGraph_not_choosable k hk⟩
    have h2 : mK k = (2 * k - 1).choose k := rfl
    omega

/-- `n(1) = 2`: a single edge with lists of size `1` can fail, and no smaller bipartite graph
does. -/
theorem listThreshold_one : listThreshold 1 = 2 := by
  have h1 := two_pow_le_listThreshold 1
  have h2 := listThreshold_le 1
  norm_num at h1
  have h3 : (2 * 1 - 1).choose 1 = 1 := rfl
  omega

end Erdos629
