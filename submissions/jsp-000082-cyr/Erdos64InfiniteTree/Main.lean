import Mathlib

/-!
# Erdős Problem #64: an infinite tree of minimum degree `3` (the infinite case is trivially false)

Erdős and Gyárfás asked whether every finite graph with minimum degree at least `3` contains a
cycle of length `2^k` for some `k ≥ 2` (OPEN for finite graphs; not addressed here, nor the
Liu–Montgomery results).  The problem page records: "An infinite tree with minimum degree `3`
shows that the answer is trivially false for infinite graphs."  This file proves that remark:
the infinite ternary tree on `ℕ` — vertex `v` adjacent to its children `3v + 1, 3v + 2, 3v + 3`
(and, for `v ≥ 1`, to its parent `(v − 1)/3`) — has every vertex of degree at least `3`, is
acyclic, and therefore has no cycle of length `2^k` for any `k`.  The cycle condition is stated in
the shape of the formal-conjectures rendering `Erdos64.erdos_64` (`∃ k v (c : G.Walk v v),
k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k`), which quantifies over finite graphs only; the infinite
graph here is our own construction.  Minimum degree is expressed without finiteness instances:
each vertex has a finite set of neighbours of size at least `3`.
-/

open SimpleGraph

/-- Adjacency of the infinite ternary tree on `ℕ`: `m` and `n` are adjacent when one is a child
`3v + 1, 3v + 2, 3v + 3` of the other. -/
def ternaryAdj (m n : ℕ) : Prop :=
  (m = 3 * n + 1 ∨ m = 3 * n + 2 ∨ m = 3 * n + 3) ∨ (n = 3 * m + 1 ∨ n = 3 * m + 2 ∨ n = 3 * m + 3)

/-- The infinite ternary tree on `ℕ`: `v` is adjacent to its children `3v + 1, 3v + 2, 3v + 3`
and (for `v ≥ 1`) to its parent. -/
def ternaryTree : SimpleGraph ℕ where
  Adj := ternaryAdj
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => by unfold ternaryAdj at h; omega⟩

/-- Adjacency in `ternaryTree` is exactly `ternaryAdj`. -/
theorem ternaryTree_adj_iff (m n : ℕ) : ternaryTree.Adj m n ↔ ternaryAdj m n := Iff.rfl

/-- A neighbour of `u` that is smaller than `u` must be the parent `(u - 1) / 3` of `u`:
the other neighbours of `u` are its children `3u + 1, 3u + 2, 3u + 3`, all larger than `u`. -/
theorem ternaryTree_eq_parent_of_adj_of_lt {u w : ℕ} (h : ternaryTree.Adj u w) (hlt : w < u) :
    w = (u - 1) / 3 := by
  rw [ternaryTree_adj_iff] at h
  unfold ternaryAdj at h
  omega

/-- Every vertex of the ternary tree has a finite neighbour set of size at least `3`. -/
theorem ternaryTree_neighbors (v : ℕ) :
    ∃ s : Finset ℕ, (∀ w, ternaryTree.Adj v w ↔ w ∈ s) ∧ 3 ≤ s.card := by
  rcases Nat.eq_zero_or_pos v with hv | hv
  · refine ⟨{1, 2, 3}, fun w => ?_, by decide⟩
    rw [ternaryTree_adj_iff]
    unfold ternaryAdj
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · refine ⟨{3 * v + 1, 3 * v + 2, 3 * v + 3, (v - 1) / 3}, fun w => ?_, ?_⟩
    · rw [ternaryTree_adj_iff]
      unfold ternaryAdj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · have hsub : ({3 * v + 1, 3 * v + 2, 3 * v + 3} : Finset ℕ) ⊆
          {3 * v + 1, 3 * v + 2, 3 * v + 3, (v - 1) / 3} := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      have hcard : ({3 * v + 1, 3 * v + 2, 3 * v + 3} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
          Finset.card_singleton]
      have hle := Finset.card_le_card hsub
      omega

/-- The ternary tree is acyclic. -/
theorem ternaryTree_isAcyclic : ternaryTree.IsAcyclic := by
  intro v c hc
  -- Rotate the cycle so that it starts at a vertex `u` of maximal label on its support.
  have hne : c.support.toFinset.Nonempty := ⟨v, by simp⟩
  set u := c.support.toFinset.max' hne with hudef
  have hu : u ∈ c.support := by
    have := Finset.max'_mem _ hne
    simpa using this
  have hmax : ∀ x ∈ c.support, x ≤ u := fun x hx => Finset.le_max' _ x (by simpa using hx)
  set d := c.rotate u hu with hddef
  have hd : d.IsCycle := hc.rotate hu
  have hdmax : ∀ x ∈ d.support, x ≤ u := fun x hx =>
    hmax x ((Walk.mem_support_rotate_iff c u hu).mp hx)
  have hnil : ¬ d.Nil := hd.not_nil
  -- Both the second and the penultimate vertex of `d` are neighbours of `u` below `u`,
  -- hence both equal the parent of `u`; but a cycle has distinct second and penultimate vertices.
  have h1 : ternaryTree.Adj u d.snd := d.adj_snd hnil
  have h2 : ternaryTree.Adj d.penultimate u := d.adj_penultimate hnil
  have hs : d.snd = (u - 1) / 3 := by
    refine ternaryTree_eq_parent_of_adj_of_lt h1 ?_
    have := hdmax d.snd (d.getVert_mem_support 1)
    exact lt_of_le_of_ne this h1.ne'
  have hp : d.penultimate = (u - 1) / 3 := by
    refine ternaryTree_eq_parent_of_adj_of_lt h2.symm ?_
    have := hdmax d.penultimate (d.getVert_mem_support (d.length - 1))
    exact lt_of_le_of_ne this h2.ne
  exact hd.snd_ne_penultimate (hs.trans hp.symm)

/-- **Erdős #64, the page's remark**: there is an infinite graph with minimum degree at least `3`
(every vertex has at least three neighbours) and no cycle of length `2^k` for any `k ≥ 2` (indeed
no cycle at all). -/
theorem erdos_64_infinite_counterexample :
    ∃ (V : Type) (G : SimpleGraph V), Infinite V ∧
      (∀ v : V, ∃ s : Finset V, (∀ w, G.Adj v w ↔ w ∈ s) ∧ 3 ≤ s.card) ∧
      G.IsAcyclic ∧
      ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  exact ⟨ℕ, ternaryTree, inferInstance, ternaryTree_neighbors, ternaryTree_isAcyclic,
    fun ⟨_, _, c, _, hc, _⟩ => ternaryTree_isAcyclic c hc⟩
