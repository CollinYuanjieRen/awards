import Mathlib

/-!
# Erdős Problem #744: odd cycles show `f_3(n) = 1`

Erdős, Hajnal and Szemerédi define `f_k(n)` as the minimal `m` such that there is a graph `G` on
`n` vertices with chromatic number `k`, such that every proper subgraph has chromatic number
`< k`, and `G` can be made bipartite by deleting `m` edges; they asked whether `f_k(n) → ∞`
(DISPROVED by Rödl–Tuza, who showed `f_k(n) = C(k−1, 2)` for large `n`; NOT formalized here).
The problem page records "Odd cycles show that `f_3(n) = 1`."  This file proves that statement
for every odd `n ≥ 3` (the only `n` for which a `3`-critical graph on `n` vertices exists, since
the `3`-critical graphs are exactly the odd cycles; for even `n` the set in the definition of
`f_3(n)` is empty).

Definitions (ours; there is no formal-conjectures rendering of this problem).  A graph `G` is
`k`-*critical*, `IsCritical k G`, if `G.chromaticNumber = k` and every proper subgraph has
chromatic number `< k`; since every proper subgraph is contained in `G − e` for an edge `e` or in
`G − v` for a vertex `v`, and the chromatic number is monotone, this is spelled out as: deleting
any edge, or deleting any vertex (`G.induce {v}ᶜ`), lowers the chromatic number below `k`.
`DeletionSet k n` is the set of `m` such that some `k`-critical graph on `Fin n` becomes
bipartite (`Colorable 2`) after deleting a set of `m` of its edges, and `f k n = sInf
(DeletionSet k n)`.

The odd cycle `cycleGraph n` has chromatic number `3` (Mathlib), deleting any edge or any vertex
leaves a path (`2`-colourable by alternating colours along the path), and deleting one edge makes
it bipartite; deleting `0` edges does not, since `G` itself is not `2`-colourable.  Hence
`IsLeast (DeletionSet 3 n) 1` and `f 3 n = 1`.
-/

namespace Erdos744

open SimpleGraph

/-- `G` is `k`-critical: its chromatic number is `k` and deleting any edge or any vertex lowers
the chromatic number below `k` (equivalently, every proper subgraph has chromatic number `< k`). -/
def IsCritical (k : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = k ∧ (∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < k) ∧
    ∀ v : V, (G.induce ({v}ᶜ : Set V)).chromaticNumber < k

/-- The numbers `m` such that some `k`-critical graph on `n` vertices can be made bipartite by
deleting `m` of its edges. -/
def DeletionSet (k n : ℕ) : Set ℕ :=
  {m | ∃ G : SimpleGraph (Fin n), IsCritical k G ∧
    ∃ S : Finset (Sym2 (Fin n)), (S : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ S.card = m ∧
      (G.deleteEdges S).Colorable 2}

/-- `f k n = min DeletionSet k n` (Erdős–Hajnal–Szemerédi). -/
noncomputable def f (k n : ℕ) : ℕ := sInf (DeletionSet k n)

/-- If `m < 2 * n` then `m % n` is `m` or `m - n`; lets `omega` handle `%` for a variable
modulus. -/
theorem mod_of_lt_two_mul {n m : ℕ} (h : m < 2 * n) :
    m % n = if m < n then m else m - n := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt h1), Nat.mod_eq_of_lt (by omega)]

/-- The `ℕ`-level content of `Fin n` subtraction being `1`: `(n - b + a) % n = 1` says exactly
that `a` is the cyclic successor of `b`. -/
theorem mod_succ_eq_iff {n a b : ℕ} (hn : 2 ≤ n) (ha : a < n) (hb : b < n) :
    (n - b + a) % n = 1 ↔ a = (b + 1) % n := by
  rw [mod_of_lt_two_mul (by omega : n - b + a < 2 * n),
    mod_of_lt_two_mul (by omega : b + 1 < 2 * n)]
  split_ifs <;> omega

/-- The cycle graph on fewer than two vertices has no edges. -/
theorem two_le_of_cycleGraph_adj : ∀ {n : ℕ} {u v : Fin n}, (cycleGraph n).Adj u v → 2 ≤ n
  | 0, u, _, _ => u.elim0
  | 1, _, _, h => absurd h cycleGraph_one_adj
  | _ + 2, _, _, _ => by omega

/-- Adjacency in `C_n` in terms of `Fin.val`: `u` and `v` are adjacent iff one is the cyclic
successor of the other. -/
theorem cycleGraph_adj_val {n : ℕ} (hn : 2 ≤ n) {u v : Fin n} :
    (cycleGraph n).Adj u v ↔ (u : ℕ) = ((v : ℕ) + 1) % n ∨ (v : ℕ) = ((u : ℕ) + 1) % n := by
  rw [cycleGraph_adj', Fin.sub_def, Fin.sub_def]
  simp only []
  rw [mod_succ_eq_iff hn u.isLt v.isLt, mod_succ_eq_iff hn v.isLt u.isLt]

/-- The position of `j` along the path obtained by cutting `C_n` between `a` and `a + 1`, i.e.
the number of steps from `a + 1` to `j` in the cyclic order. -/
def cycPos (n a j : ℕ) : ℕ := if a < j then j - a - 1 else j + n - a - 1

/-- Moving to the cyclic successor increases the position by one, except at the cut vertex `a`. -/
theorem cycPos_succ {n a x : ℕ} (hn : 2 ≤ n) (ha : a < n) (hx : x < n) (hxa : x ≠ a) :
    cycPos n a ((x + 1) % n) = cycPos n a x + 1 := by
  unfold cycPos
  rw [mod_of_lt_two_mul (by omega : x + 1 < 2 * n)]
  split_ifs <;> omega

/-- A graph mapping into `C_n` by `φ` in an adjacency-preserving way, and using no edge of `C_n`
directed from the cut vertex `a` to its successor, is `2`-colourable: colour by the parity of the
position along the cut path. -/
theorem colorable_two_of_cut {V : Type*} (n : ℕ) (hn : 2 ≤ n) (a : Fin n)
    (G : SimpleGraph V) (φ : V → Fin n)
    (hφ : ∀ {x y : V}, G.Adj x y → (cycleGraph n).Adj (φ x) (φ y))
    (hcut : ∀ {x y : V}, G.Adj x y → ¬((φ x : ℕ) = (a : ℕ) ∧ (φ y : ℕ) = ((a : ℕ) + 1) % n)) :
    G.Colorable 2 := by
  refine ⟨Coloring.mk (fun x => (⟨cycPos n a (φ x) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)) ?_⟩
  intro x y hxy
  have key : ∀ {u v : V}, G.Adj u v → (φ v : ℕ) = ((φ u : ℕ) + 1) % n →
      cycPos n a (φ v) = cycPos n a (φ u) + 1 := by
    intro u v huv hv
    have hua : (φ u : ℕ) ≠ (a : ℕ) := fun h => hcut huv ⟨h, by rw [hv, h]⟩
    rw [hv, cycPos_succ hn a.isLt (φ u).isLt hua]
  have hne : cycPos n a (φ x) % 2 ≠ cycPos n a (φ y) % 2 := by
    rcases (cycleGraph_adj_val hn).mp (hφ hxy) with h | h
    · have := key hxy.symm h; omega
    · have := key hxy h; omega
  simpa using hne

/-- Deleting any edge from the cycle `C_n` leaves a `2`-colourable graph. -/
theorem cycleGraph_deleteEdges_colorable (n : ℕ) (e : Sym2 (Fin n)) (he : e ∈ (cycleGraph n).edgeSet) :
    ((cycleGraph n).deleteEdges {e}).Colorable 2 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeSet] at he
    have hn : 2 ≤ n := two_le_of_cycleGraph_adj he
    rcases (cycleGraph_adj_val hn).mp he with h | h
    · refine colorable_two_of_cut n hn v _ id (fun hxy => (deleteEdges_adj.mp hxy).1) ?_
      rintro x y hxy ⟨hx, hy⟩
      simp only [id_eq] at hx hy
      refine (deleteEdges_adj.mp hxy).2 ?_
      have hx' : x = v := Fin.ext hx
      have hy' : y = u := Fin.ext (by rw [hy, ← h])
      subst hx'; subst hy'
      simp [Sym2.eq_swap]
    · refine colorable_two_of_cut n hn u _ id (fun hxy => (deleteEdges_adj.mp hxy).1) ?_
      rintro x y hxy ⟨hx, hy⟩
      simp only [id_eq] at hx hy
      refine (deleteEdges_adj.mp hxy).2 ?_
      have hx' : x = u := Fin.ext hx
      have hy' : y = v := Fin.ext (by rw [hy, ← h])
      subst hx'; subst hy'
      simp

/-- Deleting any vertex from the cycle `C_n` leaves a `2`-colourable graph. -/
theorem cycleGraph_induce_colorable (n : ℕ) (v : Fin n) :
    ((cycleGraph n).induce ({v}ᶜ : Set (Fin n))).Colorable 2 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · refine ⟨Coloring.mk (fun _ => 0) ?_⟩
    intro x y hxy
    exact absurd (two_le_of_cycleGraph_adj (show (cycleGraph n).Adj ↑x ↑y from hxy)) (by omega)
  · refine colorable_two_of_cut n hn v _ Subtype.val (fun hxy => hxy) ?_
    rintro x y hxy ⟨hx, -⟩
    have hx2 := x.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx2
    exact hx2 (Fin.ext hx)

/-- Odd cycles are `3`-critical. -/
theorem cycleGraph_isCritical (n : ℕ) (h3 : 3 ≤ n) (hodd : Odd n) : IsCritical 3 (cycleGraph n) := by
  refine ⟨by simpa using chromaticNumber_cycleGraph_of_odd n (by omega) hodd, fun e he => ?_,
    fun v => ?_⟩
  · exact lt_of_le_of_lt
      (chromaticNumber_le_iff_colorable.mpr (cycleGraph_deleteEdges_colorable n e he))
      (by norm_num)
  · exact lt_of_le_of_lt
      (chromaticNumber_le_iff_colorable.mpr (cycleGraph_induce_colorable n v)) (by norm_num)

/-- No `3`-critical graph is bipartite, so `0 ∉ DeletionSet 3 n`. -/
theorem zero_notMem_deletionSet (n : ℕ) : 0 ∉ DeletionSet 3 n := by
  rintro ⟨G, ⟨hχ, -, -⟩, S, -, hS, hcol⟩
  rw [Finset.card_eq_zero] at hS
  subst hS
  rw [Finset.coe_empty, deleteEdges_empty, ← chromaticNumber_le_iff_colorable, hχ] at hcol
  norm_num at hcol

/-- **Erdős #744, "odd cycles show `f_3(n) = 1`"**: for odd `n ≥ 3`, `1` is the least element of
`DeletionSet 3 n`, and `f 3 n = 1`. -/
theorem erdos_744_f_three (n : ℕ) (h3 : 3 ≤ n) (hodd : Odd n) :
    IsLeast (DeletionSet 3 n) 1 ∧ f 3 n = 1 := by
  have hn2 : 2 ≤ n := by omega
  have hadj : (cycleGraph n).Adj (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ := by
    rw [cycleGraph_adj_val hn2]
    exact Or.inr (by simp [Nat.mod_eq_of_lt hn2])
  have hmem : (1 : ℕ) ∈ DeletionSet 3 n := by
    refine ⟨cycleGraph n, cycleGraph_isCritical n h3 hodd,
      {s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n))}, ?_, Finset.card_singleton _, ?_⟩
    · rw [Finset.coe_singleton, Set.singleton_subset_iff, mem_edgeSet]
      exact hadj
    · rw [Finset.coe_singleton]
      exact cycleGraph_deleteEdges_colorable n _ (by rw [mem_edgeSet]; exact hadj)
  have hleast : IsLeast (DeletionSet 3 n) 1 := by
    refine ⟨hmem, fun m hm => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact absurd hm (zero_notMem_deletionSet n)
    · exact hpos
  exact ⟨hleast, hleast.csInf_eq⟩

end Erdos744

open Erdos744 in
/-- **Erdős #744, closed form**: for every odd `n ≥ 3`, `f_3(n) = 1` (with `1` the least element of
the defining set). -/
theorem erdos_744_f_three_closed :
    ¬ ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ ¬ (IsLeast (DeletionSet 3 n) 1 ∧ f 3 n = 1) := by
  rintro ⟨n, h3, hodd, h⟩
  exact h (Erdos744.erdos_744_f_three n h3 hodd)
