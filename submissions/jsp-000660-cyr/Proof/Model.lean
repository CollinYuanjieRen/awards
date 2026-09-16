import Mathlib
import Proof.Defs

/-!
# Alon's random bipartite model

For `n` vertices `A = Fin n` and block indices `i ∈ [4, top n]`, `j ∈ Fin 8` (with
`top n = ⌊log₂ n⌋ / 2`), block `(i, j)` has `bsize n (i, j) = n / 2 ^ i` vertices.  A choice
function `f : Choice n` assigns to every `a ∈ A` and every block one vertex of that block; the
graph `graphOf f` joins `a` to each of its chosen vertices.  Every `a` has degree
`8 * (top n - 3)`, the graph is bipartite between `A` and the blocks, and between a fixed set
`A'` of `A`-vertices and a fixed block there are at most `|A'|` edges.
-/

open SimpleGraph Finset

namespace Erdos803

/-- The largest block index: `⌊log₂ n⌋ / 2`. -/
def top (n : ℕ) : ℕ := Nat.log 2 n / 2

/-- Block indices `(i, j)` with `4 ≤ i ≤ top n` and `j < 8`. -/
abbrev BlockIdx (n : ℕ) := ↥(Finset.Icc 4 (top n)) × Fin 8

/-- The size `n / 2 ^ i` of block `(i, j)`. -/
def bsize (n : ℕ) (p : BlockIdx n) : ℕ := n / 2 ^ p.1.1

/-- The block vertices: a block index together with a position in the block. -/
abbrev BVertex (n : ℕ) := Σ p : BlockIdx n, Fin (bsize n p)

/-- The vertex type: `A = Fin n` plus the block vertices. -/
abbrev Vtx (n : ℕ) := Fin n ⊕ BVertex n

/-- A choice function: for every `a ∈ A` and every block, one vertex of that block. -/
abbrev Choice (n : ℕ) := Fin n → (p : BlockIdx n) → Fin (bsize n p)

/-- The adjacency relation of the random graph: `a` is joined to its chosen vertex in each block. -/
def adj {n : ℕ} (f : Choice n) : Vtx n → Vtx n → Prop
  | Sum.inl a, Sum.inr ⟨p, b⟩ => f a p = b
  | Sum.inr ⟨p, b⟩, Sum.inl a => f a p = b
  | _, _ => False

theorem adj_symm {n : ℕ} (f : Choice n) : ∀ ⦃u v : Vtx n⦄, adj f u v → adj f v u := by
  rintro (a | ⟨p, b⟩) (a' | ⟨p', b'⟩) h
  · exact h
  · exact h
  · exact h
  · exact h

theorem adj_irrefl {n : ℕ} (f : Choice n) : ∀ u : Vtx n, ¬ adj f u u := by
  rintro (a | ⟨p, b⟩) h
  · exact h
  · exact h

/-- The graph determined by a choice function. -/
def graphOf {n : ℕ} (f : Choice n) : SimpleGraph (Vtx n) where
  Adj := adj f
  symm := ⟨fun _ _ h => adj_symm f h⟩
  loopless := ⟨fun u h => adj_irrefl f u h⟩

theorem graphOf_adj_inl_inr {n : ℕ} (f : Choice n) (a : Fin n) (p : BlockIdx n)
    (b : Fin (bsize n p)) : (graphOf f).Adj (Sum.inl a) (Sum.inr ⟨p, b⟩) ↔ f a p = b :=
  Iff.rfl

theorem graphOf_not_adj_inl_inl {n : ℕ} (f : Choice n) (a a' : Fin n) :
    ¬ (graphOf f).Adj (Sum.inl a) (Sum.inl a') := fun h ↦ h

theorem graphOf_not_adj_inr_inr {n : ℕ} (f : Choice n) (b b' : BVertex n) :
    ¬ (graphOf f).Adj (Sum.inr b) (Sum.inr b') := by
  obtain ⟨p, c⟩ := b
  obtain ⟨p', c'⟩ := b'
  exact fun h ↦ h

/-- The number of block indices. -/
theorem card_blockIdx (n : ℕ) : Fintype.card (BlockIdx n) = 8 * (top n + 1 - 4) := by
  rw [Fintype.card_prod, Fintype.card_coe, Nat.card_Icc, Fintype.card_fin, mul_comm]

/-- The number of edges of `graphOf f`: every `a ∈ A` contributes one edge per block. -/
theorem edgeSet_ncard_graphOf {n : ℕ} (f : Choice n) :
    (graphOf f).edgeSet.ncard = n * Fintype.card (BlockIdx n) := by
  set g : Fin n × BlockIdx n → Sym2 (Vtx n) :=
    fun ap ↦ s(Sum.inl ap.1, Sum.inr ⟨ap.2, f ap.1 ap.2⟩) with hg
  have hinj : Function.Injective g := by
    rintro ⟨a, p⟩ ⟨a', p'⟩ h
    simp only [hg, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.injEq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · obtain ⟨h3, -⟩ := h2
      exact Prod.ext h1 h3
    · exact absurd h1 (by simp)
  have hset : (graphOf f).edgeSet = Set.range g := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · intro e
      induction e using Sym2.ind with
      | _ u v =>
        intro h
        rw [SimpleGraph.mem_edgeSet] at h
        rcases u with a | ⟨p, b⟩ <;> rcases v with a' | ⟨p', b'⟩
        · exact absurd h (graphOf_not_adj_inl_inl f a a')
        · rw [graphOf_adj_inl_inr] at h
          subst h
          exact ⟨(a, p'), rfl⟩
        · have h' := h.symm
          rw [graphOf_adj_inl_inr] at h'
          subst h'
          exact ⟨(a', p), Sym2.eq_swap⟩
        · exact absurd h (graphOf_not_adj_inr_inr f ⟨p, b⟩ ⟨p', b'⟩)
    · rintro e ⟨⟨a, p⟩, rfl⟩
      rw [hg, SimpleGraph.mem_edgeSet]
      exact (graphOf_adj_inl_inr f a p _).mpr rfl
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin]

/-- A geometric bound in `ℕ`: `∑_{k < K} ⌊m / 2 ^ k⌋ ≤ 2 * m`. -/
private lemma sum_range_div_two_pow_le (K m : ℕ) :
    ∑ k ∈ Finset.range K, m / 2 ^ k ≤ 2 * m := by
  induction K generalizing m with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ']
    have h : ∀ k : ℕ, m / 2 ^ (k + 1) = m / 2 / 2 ^ k := by
      intro k
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    simp only [h, pow_zero, Nat.div_one]
    have := ih (m / 2)
    omega

/-- The tail bound `8 * ∑_{i ∈ [4, T]} ⌊n / 2 ^ i⌋ ≤ n`. -/
private lemma eight_mul_sum_Icc_div_le (n T : ℕ) :
    8 * ∑ i ∈ Finset.Icc 4 T, n / 2 ^ i ≤ n := by
  have h : ∑ i ∈ Finset.Icc 4 T, n / 2 ^ i
      = ∑ k ∈ Finset.range (T + 1 - 4), n / 16 / 2 ^ k := by
    have hIco : Finset.Icc 4 T = Finset.Ico 4 (T + 1) := by
      ext i
      simp
    rw [hIco, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.div_div_eq_div_mul, pow_add]
    norm_num
  rw [h]
  calc 8 * ∑ k ∈ Finset.range (T + 1 - 4), n / 16 / 2 ^ k
      ≤ 8 * (2 * (n / 16)) := Nat.mul_le_mul_left _ (sum_range_div_two_pow_le _ _)
    _ ≤ n := by omega

/-- There are at most `n` block vertices (`8 ∑_{i ≥ 4} n / 2 ^ i ≤ n`). -/
theorem card_bVertex_le (n : ℕ) : Fintype.card (BVertex n) ≤ n := by
  have hcard : Fintype.card (BVertex n) = 8 * ∑ i ∈ Finset.Icc 4 (top n), n / 2 ^ i := by
    rw [Fintype.card_sigma, Fintype.sum_prod_type, Finset.mul_sum, Finset.univ_eq_attach,
      ← Finset.sum_attach (Finset.Icc 4 (top n)) fun i ↦ 8 * (n / 2 ^ i)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [Fintype.card_fin]
    simp [bsize]
  rw [hcard]
  exact eight_mul_sum_Icc_div_le n (top n)

theorem card_vtx_le (n : ℕ) : Fintype.card (Vtx n) ≤ 2 * n := by
  rw [Fintype.card_sum, Fintype.card_fin]
  have := card_bVertex_le n
  omega

/-- Every block has at least `√n / 2` vertices: `n ≤ 4 * bsize n p ^ 2` (for `4 ≤ n`). -/
theorem le_four_mul_bsize_sq {n : ℕ} (hn : 4 ≤ n) (p : BlockIdx n) : n ≤ 4 * bsize n p ^ 2 := by
  have hi : (p.1 : ℕ) ≤ top n := (Finset.mem_Icc.mp p.1.2).2
  have hq : 2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ) ≤ n := by
    have h2 : 2 * (p.1 : ℕ) ≤ Nat.log 2 n := by
      have : (p.1 : ℕ) ≤ Nat.log 2 n / 2 := hi
      omega
    calc 2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ) = 2 ^ (2 * (p.1 : ℕ)) := by ring
      _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) h2
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hqpos : 0 < 2 ^ (p.1 : ℕ) := pow_pos (by norm_num) _
  have hd : 1 ≤ bsize n p := by
    rw [bsize, Nat.one_le_div_iff hqpos]
    calc 2 ^ (p.1 : ℕ) = 1 * 2 ^ (p.1 : ℕ) := (one_mul _).symm
      _ ≤ 2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ) := Nat.mul_le_mul_right _ hqpos
      _ ≤ n := hq
  have hlt : n < (bsize n p + 1) * 2 ^ (p.1 : ℕ) := by
    rw [bsize, add_mul, one_mul]
    exact Nat.lt_div_mul_add hqpos
  have key : n * n < (bsize n p + 1) ^ 2 * n := by
    calc n * n < ((bsize n p + 1) * 2 ^ (p.1 : ℕ)) * ((bsize n p + 1) * 2 ^ (p.1 : ℕ)) :=
          Nat.mul_lt_mul_of_lt_of_lt hlt hlt
      _ = (bsize n p + 1) ^ 2 * (2 ^ (p.1 : ℕ) * 2 ^ (p.1 : ℕ)) := by ring
      _ ≤ (bsize n p + 1) ^ 2 * n := Nat.mul_le_mul_left _ hq
  have hn2 : n < (bsize n p + 1) ^ 2 := Nat.lt_of_mul_lt_mul_right key
  nlinarith [hd, hn2]

/-- The number of `graphOf f`-edges between a set `A'` of `A`-vertices and one block `p`
is at most `|A'|`. -/
theorem card_edges_block_le {n : ℕ} (f : Choice n) (A' : Finset (Fin n)) (p : BlockIdx n) :
    ((A' ×ˢ (Finset.univ : Finset (Fin (bsize n p)))).filter
      fun ab ↦ f ab.1 p = ab.2).card ≤ A'.card := by
  classical
  refine Finset.card_le_card_of_injOn Prod.fst (fun ab hab ↦ ?_) (fun ab hab ab' hab' h ↦ ?_)
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
  · rw [Finset.mem_coe, Finset.mem_filter] at hab hab'
    exact Prod.ext h (by rw [← hab.2, ← hab'.2, h])

end Erdos803
