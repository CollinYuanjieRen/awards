import CameronErdos.Counting.Basic
import CameronErdos.Part2.Cor13Even

/-!
# `Lem_Cor13_Matching` — Green's Corollary 13, the "small element" matching

Green, *The Cameron–Erdős conjecture* (2004), p. 11, proof of Corollary 13.

In the first alternative of Proposition 7 one knows that a sum-free `A ⊆ [1, N]` has only
few elements below a threshold `w`.  If `A` additionally contains some *small* element
`t` (`3 t ≤ N`), then the part of `A` lying in the window `[w, N]` must avoid a large
matching: Green produces `⌊N/12⌋ - 4` totally disjoint pairs `(x, x + t)` with `x ≥ N/2`.
Here we produce `⌊N/8⌋ - 4` such pairs, which is also achievable and gives a stronger
bound.

The pairs are `{x_i, x_i + t}` with

  `x_i = N/2 + 2 t ⌊i / t⌋ + (i mod t)`  (`windowPoint N t i`),

i.e. the `i`-th element of the union of the blocks `[N/2 + 2bt, N/2 + (2b+1)t)`; the pair
translates such a block onto the next one, so the pairs are pairwise disjoint.  Since
`t ∈ A` and `A` is sum-free, `x_i ∈ A` would force `x_i + t ∉ A`, so no pair is contained
in `A`.

`card_avoiding_matching_fin` then bounds the number of admissible windows by
`3 ^ q · 2 ^ (|[w, N]| - 2q)` with `q = ⌊N/8⌋ - 4`, and the (at most `k`-element) part of
`A` outside the window is one of at most `∑_{j ≤ k} C(N, j)` sets.

Main results: `CameronErdos.exists_window_matching` and
`CameronErdos.card_smallElemFamily_le`.
-/

open Finset

namespace CameronErdos

/-! ## The block function used for the window matching -/

/-- `windowPoint N t i` enumerates the elements of the blocks
`[N/2 + 2 t b, N/2 + 2 t b + t)`, `b = 0, 1, 2, …`: writing `i = t b + a` with `a < t`,
`windowPoint N t i = N/2 + 2 t b + a`.  Consecutive values inside a block differ by less
than `t`, and the `t`-translate of a block is the next half-block; hence the pairs
`{windowPoint N t i, windowPoint N t i + t}` are pairwise disjoint. -/
def windowPoint (N t i : ℕ) : ℕ := N / 2 + 2 * (t * (i / t)) + i % t

/-- The key gap property: for `i ≠ j` the four points `windowPoint N t i`,
`windowPoint N t i + t`, `windowPoint N t j`, `windowPoint N t j + t` split into two
disjoint pairs. -/
lemma windowPoint_gap (N t : ℕ) (ht : 0 < t) (i j : ℕ) (hij : i ≠ j) :
    windowPoint N t i ≠ windowPoint N t j ∧
      windowPoint N t i + t ≠ windowPoint N t j ∧
      windowPoint N t j + t ≠ windowPoint N t i ∧
      windowPoint N t i + t ≠ windowPoint N t j + t := by
  have hi := Nat.div_add_mod i t
  have hj := Nat.div_add_mod j t
  have hmi : i % t < t := Nat.mod_lt _ ht
  have hmj : j % t < t := Nat.mod_lt _ ht
  have key : t * (i / t) = t * (j / t) ∨ t * (i / t) + t ≤ t * (j / t) ∨
      t * (j / t) + t ≤ t * (i / t) := by
    rcases lt_trichotomy (i / t) (j / t) with h | h | h
    · refine Or.inr (Or.inl ?_)
      have he : t * (i / t) + t = t * (i / t + 1) := by ring
      rw [he]
      exact Nat.mul_le_mul_left t (by omega)
    · exact Or.inl (by rw [h])
    · refine Or.inr (Or.inr ?_)
      have he : t * (j / t) + t = t * (j / t + 1) := by ring
      rw [he]
      exact Nat.mul_le_mul_left t (by omega)
  obtain ⟨u, hu⟩ : ∃ u, t * (i / t) = u := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, t * (j / t) = v := ⟨_, rfl⟩
  rw [hu] at hi key
  rw [hv] at hj key
  unfold windowPoint
  rw [hu, hv]
  omega

/-- All `⌊N/8⌋ - 4` pairs live inside the window `[N/2, N]`. -/
lemma windowPoint_mem (N t i : ℕ) (ht1 : 1 ≤ t) (ht : 3 * t ≤ N) (hN : 64 ≤ N)
    (hi : i < N / 8 - 4) :
    N / 2 ≤ windowPoint N t i ∧ windowPoint N t i + t ≤ N := by
  have hd := Nat.div_add_mod i t
  have hm : i % t < t := Nat.mod_lt _ ht1
  obtain ⟨u, hu⟩ : ∃ u, t * (i / t) = u := ⟨_, rfl⟩
  rw [hu] at hd
  have hcase : u = 0 ∨ t ≤ u := by
    rcases Nat.eq_zero_or_pos (i / t) with h | h
    · exact Or.inl (by rw [← hu, h, Nat.mul_zero])
    · refine Or.inr ?_
      have h1 : t * 1 ≤ t * (i / t) := Nat.mul_le_mul_left t h
      rw [hu, Nat.mul_one] at h1
      exact h1
  unfold windowPoint
  rw [hu]
  rcases hcase with h | h
  · subst h; omega
  · omega

/-! ## `Lem_Cor13_Matching`: the matching avoided by the window of `A` -/

/-- **Green's window matching** (Green 2004, p. 11).  For every `t` with `1 ≤ t` and
`3 t ≤ N` (and `N ≥ 64`) there are `⌊N/8⌋ - 4` pairwise disjoint two-element subsets of
`[N/2, N]`, none of which can be contained in a sum-free set containing `t`.

The pairs are `{x, x + t}` with `x = windowPoint N t i`. -/
theorem exists_window_matching (N t : ℕ) (ht1 : 1 ≤ t) (ht : 3 * t ≤ N) (hN : 64 ≤ N) :
    ∃ P : Fin (N / 8 - 4) → Finset ℕ,
      (∀ i, P i ⊆ Finset.Icc (N / 2) N) ∧
      (∀ i, #(P i) = 2) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (∀ i, ∀ A : Finset ℕ, IsSumFree A → t ∈ A → ¬ P i ⊆ A) := by
  classical
  refine ⟨fun i => ({windowPoint N t (i : ℕ), windowPoint N t (i : ℕ) + t} : Finset ℕ),
    ?_, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨hlo, hhi⟩ := windowPoint_mem N t (i : ℕ) ht1 ht hN i.isLt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Icc]
    rcases hx with rfl | rfl <;> omega
  · intro i
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega),
      Finset.card_singleton]
  · intro i j hij
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    obtain ⟨g1, g2, g3, g4⟩ := windowPoint_gap N t ht1 (i : ℕ) (j : ℕ) hij'
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, not_or]
    rintro x (rfl | rfl) <;> exact ⟨by omega, by omega⟩
  · intro i A hA htA hsub
    have h1 : windowPoint N t (i : ℕ) ∈ A := hsub (by simp)
    have h2 : windowPoint N t (i : ℕ) + t ∈ A := hsub (by simp)
    exact hA _ h1 _ htA h2

/-! ## The family being counted -/

/-- The sum-free subsets `A ⊆ [1, N]` with at most `k` elements outside the window
`[w, N]` and containing at least one *small* element `t` (`3 t ≤ N`). -/
noncomputable def SmallElemFamily (N w k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    (fun A => IsSumFree A ∧ #(A \ Finset.Icc w N) ≤ k ∧ ∃ t ∈ A, 3 * t ≤ N)

lemma mem_smallElemFamily {N w k : ℕ} {A : Finset ℕ} :
    A ∈ SmallElemFamily N w k ↔
      A ⊆ Finset.Icc 1 N ∧ IsSumFree A ∧ #(A \ Finset.Icc w N) ≤ k ∧
        ∃ t ∈ A, 3 * t ≤ N := by
  classical
  rw [SmallElemFamily, Finset.mem_filter, Finset.mem_powerset]

/-- For a fixed small element `t` the number of members of `SmallElemFamily N w k`
containing `t` is at most `(∑_{j ≤ k} C(N, j)) · 3 ^ q · 2 ^ ((N + 1 - w) - 2 q)` with
`q = ⌊N/8⌋ - 4`: the part of `A` outside the window is one of at most `∑_{j ≤ k} C(N, j)`
sets, and the part inside avoids the matching of `exists_window_matching`. -/
theorem card_smallElemFiber_le (N w k t : ℕ) (hN : 64 ≤ N) (hw : w ≤ N / 2)
    (ht1 : 1 ≤ t) (ht3 : 3 * t ≤ N) :
    #{A ∈ SmallElemFamily N w k | t ∈ A} ≤
      (∑ j ∈ Finset.range (k + 1), N.choose j) *
        (3 ^ (N / 8 - 4) * 2 ^ ((N + 1 - w) - 2 * (N / 8 - 4))) := by
  classical
  obtain ⟨P, hPsub, hPcard, hPdisj, hPavoid⟩ := exists_window_matching N t ht1 ht3 hN
  have hPW : ∀ i, P i ⊆ Finset.Icc w N := by
    intro i x hx
    have hx' := hPsub i hx
    simp only [Finset.mem_Icc] at hx' ⊢
    omega
  have hcount := card_avoiding_matching_fin (Finset.Icc w N) P hPW hPcard hPdisj
  rw [Nat.card_Icc] at hcount
  have hScard : #{E ∈ (Finset.Icc 1 N).powerset | #E ≤ k}
      ≤ ∑ j ∈ Finset.range (k + 1), N.choose j := by
    have h := card_powerset_card_le (Finset.Icc 1 N) k
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hmain : #{A ∈ SmallElemFamily N w k | t ∈ A} ≤
      #(({E ∈ (Finset.Icc 1 N).powerset | #E ≤ k}) ×ˢ
        ({X ∈ (Finset.Icc w N).powerset | ∀ i, ¬ P i ⊆ X})) := by
    refine Finset.card_le_card_of_injOn
      (fun A => (A \ Finset.Icc w N, A ∩ Finset.Icc w N)) ?_ ?_
    · intro A hA
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hA
      obtain ⟨hAfam, htA⟩ := hA
      obtain ⟨hAsub, hAsf, hAk, -⟩ := mem_smallElemFamily.1 hAfam
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨⟨Finset.sdiff_subset.trans hAsub, hAk⟩, Finset.inter_subset_right, ?_⟩
      intro i hsubi
      exact hPavoid i A hAsf htA (hsubi.trans Finset.inter_subset_left)
    · intro A _ B _ hAB
      simp only [Prod.mk.injEq] at hAB
      have hA' : A \ Finset.Icc w N ∪ A ∩ Finset.Icc w N = A :=
        Finset.sdiff_union_inter A (Finset.Icc w N)
      have hB' : B \ Finset.Icc w N ∪ B ∩ Finset.Icc w N = B :=
        Finset.sdiff_union_inter B (Finset.Icc w N)
      rw [← hA', ← hB', hAB.1, hAB.2]
  rw [Finset.card_product, hcount] at hmain
  exact hmain.trans (Nat.mul_le_mul hScard le_rfl)

/-- **`Lem_Cor13_Matching`** (Green 2004, Cor. 13, first alternative).

The sum-free subsets `A ⊆ [1, N]` with at most `k` elements outside the window `[w, N]`
and containing a small element `t` (`3 t ≤ N`) number at most
`N · (∑_{j ≤ k} C(N, j)) · 3 ^ (⌊N/8⌋ - 4) · 2 ^ ((N + 1 - w) - 2 (⌊N/8⌋ - 4))`.

Here `N + 1 - w = |[w, N]|` is the size of the window and all divisions are
natural-number divisions. -/
theorem card_smallElemFamily_le (N w k : ℕ) (hN : 64 ≤ N) (hw : w ≤ N / 2) :
    #(SmallElemFamily N w k) ≤
      N * (∑ j ∈ Finset.range (k + 1), N.choose j) * 3 ^ (N / 8 - 4) *
        2 ^ ((N + 1 - w) - 2 * (N / 8 - 4)) := by
  classical
  set B : ℕ := (∑ j ∈ Finset.range (k + 1), N.choose j) *
    (3 ^ (N / 8 - 4) * 2 ^ ((N + 1 - w) - 2 * (N / 8 - 4))) with hB
  have hcover : SmallElemFamily N w k ⊆
      (Finset.Icc 1 (N / 3)).biUnion (fun t => {A ∈ SmallElemFamily N w k | t ∈ A}) := by
    intro A hA
    obtain ⟨hAsub, -, -, t, htA, ht3⟩ := mem_smallElemFamily.1 hA
    have htmem : t ∈ Finset.Icc 1 (N / 3) := by
      have hb := hAsub htA
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    exact Finset.mem_biUnion.2 ⟨t, htmem, Finset.mem_filter.2 ⟨hA, htA⟩⟩
  calc #(SmallElemFamily N w k)
      ≤ #((Finset.Icc 1 (N / 3)).biUnion
          (fun t => {A ∈ SmallElemFamily N w k | t ∈ A})) := Finset.card_le_card hcover
    _ ≤ ∑ t ∈ Finset.Icc 1 (N / 3), #{A ∈ SmallElemFamily N w k | t ∈ A} :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ Finset.Icc 1 (N / 3), B := by
        refine Finset.sum_le_sum ?_
        intro t htm
        simp only [Finset.mem_Icc] at htm
        exact hB ▸ card_smallElemFiber_le N w k t hN hw htm.1 (by omega)
    _ = #(Finset.Icc 1 (N / 3)) * B := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ N * B := by
        rw [Nat.card_Icc]
        exact Nat.mul_le_mul_right _ (by omega)
    _ = N * (∑ j ∈ Finset.range (k + 1), N.choose j) * 3 ^ (N / 8 - 4) *
          2 ^ ((N + 1 - w) - 2 * (N / 8 - 4)) := by rw [hB]; ring

#print axioms windowPoint_gap
#print axioms windowPoint_mem
#print axioms exists_window_matching
#print axioms mem_smallElemFamily
#print axioms card_smallElemFiber_le
#print axioms card_smallElemFamily_le

end CameronErdos
