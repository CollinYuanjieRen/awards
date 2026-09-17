import Jsp731.Defs

/-!
# JSP-000731 / Erdős #880 — bookkeeping lemmas and the case `k = 2`

The first half of the file is general bookkeeping on the definitions of `Jsp731/Defs.lean`
(monotonicity in the number of summands, the translation between "at most `k`" and
"exactly `k`" via padding with zeros, monotonicity of `HasBoundedGaps`).

The second half is the positive answer for `k = 2` (Hegyvári–Hennecart–Plagne 2007, Theorem 1):
if `n` is **odd** and is a sum of at most two elements of `A`, then those two elements are
automatically distinct, because `a + a` is even.  Hence every large odd integer is a sum of at
most two *distinct* elements of `A`, so the windows `[n, n + 1]` eventually all meet
`distinctSums A 2`: the gaps are at most `2`.
-/

open Filter

namespace Erdos880

/-! ### General bookkeeping on the definitions -/

theorem isSumOfAtMost_mono {A : Set ℕ} {j k n : ℕ} (hjk : j ≤ k) (h : IsSumOfAtMost A j n) :
    IsSumOfAtMost A k n := by
  obtain ⟨m, hmA, hcard, hsum⟩ := h
  exact ⟨m, hmA, hcard.trans hjk, hsum⟩

theorem isSumOfAtMost_of_exactly {A : Set ℕ} {k n : ℕ} (h : IsSumOfExactly A k n) :
    IsSumOfAtMost A k n := by
  obtain ⟨m, hmA, hcard, hsum⟩ := h
  exact ⟨m, hmA, hcard.le, hsum⟩

/-- Padding with zeros: a sum of ≤ k elements of `A` is a sum of exactly `k` elements of
`insert 0 A`. -/
theorem isSumOfExactly_insert_zero {A : Set ℕ} {k n : ℕ} (h : IsSumOfAtMost A k n) :
    IsSumOfExactly (insert 0 A) k n := by
  obtain ⟨m, hmA, hcard, hsum⟩ := h
  refine ⟨m + Multiset.replicate (k - Multiset.card m) 0, ?_, ?_, ?_⟩
  · intro a ha
    rcases Multiset.mem_add.mp ha with ha | ha
    · exact Set.mem_insert_of_mem _ (hmA a ha)
    · rw [Multiset.eq_of_mem_replicate ha]
      exact Set.mem_insert _ _
  · rw [Multiset.card_add, Multiset.card_replicate]
    omega
  · rw [Multiset.sum_add, Multiset.sum_replicate, hsum, smul_zero, add_zero]

/-- Dropping the padding zeros does not change a multiset sum. -/
private theorem sum_filter_pos (m : Multiset ℕ) :
    (Multiset.filter (fun a => 0 < a) m).sum = m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : 0 < a
    · rw [Multiset.filter_cons_of_pos _ ha, Multiset.sum_cons, Multiset.sum_cons, ih]
    · rw [Multiset.filter_cons_of_neg _ ha, ih, Multiset.sum_cons, Nat.eq_zero_of_not_pos ha,
        zero_add]

/-- Removing zeros: a sum of exactly `k` elements of `insert 0 A` is a sum of ≤ k elements
of `A`. -/
theorem isSumOfAtMost_of_exactly_insert_zero {A : Set ℕ} {k n : ℕ}
    (h : IsSumOfExactly (insert 0 A) k n) : IsSumOfAtMost A k n := by
  obtain ⟨m, hmA, hcard, hsum⟩ := h
  refine ⟨Multiset.filter (fun a => 0 < a) m, ?_, ?_, ?_⟩
  · intro a ha
    have h1 : a ∈ m := Multiset.mem_of_mem_filter ha
    have h2 : 0 < a := Multiset.of_mem_filter ha
    rcases hmA a h1 with h | h
    · exact absurd h (by omega)
    · exact h
  · exact (Multiset.card_le_card (Multiset.filter_le _ m)).trans hcard.le
  · rw [sum_filter_pos, hsum]

theorem exactDistinctSums_insert_zero_subset (A : Set ℕ) (k : ℕ) :
    exactDistinctSums (insert 0 A) k ⊆ distinctSums A k := by
  intro n hn
  obtain ⟨s, hsA, hcard, hsum⟩ := hn
  refine ⟨s.erase 0, ?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_erase] at ha
    rcases hsA (by exact_mod_cast ha.2) with h | h
    · exact absurd h ha.1
    · exact h
  · exact (Finset.card_erase_le).trans hcard.le
  · rw [Finset.sum_erase s rfl]
    exact hsum

theorem hasBoundedGaps_mono {B B' : Set ℕ} (hBB' : B ⊆ B') (h : HasBoundedGaps B) :
    HasBoundedGaps B' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, hC.mono ?_⟩
  intro n hn
  obtain ⟨b, hb, h1, h2⟩ := hn
  exact ⟨b, hBB' hb, h1, h2⟩

theorem mem_distinctSums_of_mem {A : Set ℕ} {k a : ℕ} (hk : 1 ≤ k) (ha : a ∈ A) :
    a ∈ distinctSums A k := by
  refine ⟨{a}, ?_, ?_, ?_⟩
  · simpa using ha
  · simpa using hk
  · simp

theorem distinctSums_infinite_of_infinite {A : Set ℕ} {k : ℕ} (hk : 1 ≤ k) (hA : A.Infinite) :
    (distinctSums A k).Infinite :=
  hA.mono fun _ ha => mem_distinctSums_of_mem hk ha

/-! ### Order two: the positive answer -/

/-- Two distinct members of `A` give an element of `exactDistinctSums A 2`. -/
private theorem pair_mem_exactDistinctSums {A : Set ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) : a + b ∈ exactDistinctSums A 2 := by
  refine ⟨{a, b}, ?_, Finset.card_pair hab, Finset.sum_pair hab⟩
  simp [Set.insert_subset_iff, ha, hb]

theorem odd_mem_distinctSums_two {A : Set ℕ} {n : ℕ} (hn : Odd n) (h : IsSumOfAtMost A 2 n) :
    n ∈ distinctSums A 2 := by
  obtain ⟨m, hmA, hcard, hsum⟩ := h
  have hc : Multiset.card m = 0 ∨ Multiset.card m = 1 ∨ Multiset.card m = 2 := by omega
  rcases hc with hc | hc | hc
  · rw [Multiset.card_eq_zero] at hc
    rw [hc] at hsum
    simp at hsum
    rw [← hsum] at hn
    simp at hn
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
    have ha : a ∈ A := hmA a (by simp)
    rw [Multiset.sum_singleton] at hsum
    rw [← hsum]
    exact mem_distinctSums_of_mem one_le_two ha
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
    have ha : a ∈ A := hmA a (by simp)
    have hb : b ∈ A := hmA b (by simp)
    replace hsum : a + b = n := by simpa using hsum
    have hab : a ≠ b := by
      rintro rfl
      rw [Nat.odd_iff] at hn
      omega
    rw [← hsum]
    obtain ⟨s, hsA, hs2, hssum⟩ := pair_mem_exactDistinctSums ha hb hab
    exact ⟨s, hsA, hs2.le, hssum⟩

theorem odd_mem_exactDistinctSums_two {A : Set ℕ} {n : ℕ} (hn : Odd n) (h : IsSumOfExactly A 2 n) :
    n ∈ exactDistinctSums A 2 := by
  obtain ⟨m, hmA, hcard, hsum⟩ := h
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hcard
  have ha : a ∈ A := hmA a (by simp)
  have hb : b ∈ A := hmA b (by simp)
  replace hsum : a + b = n := by simpa using hsum
  have hab : a ≠ b := by
    rintro rfl
    rw [Nat.odd_iff] at hn
    omega
  rw [← hsum]
  exact pair_mem_exactDistinctSums ha hb hab

/-- Eventually every window `[n, n+1]` contains a sum of ≤ 2 distinct elements: gaps ≤ 2. -/
theorem order_two_gap_le_two (A : Set ℕ) (hA : IsAsymptoticBasis A 2) :
    ∀ᶠ n in atTop, ∃ b ∈ distinctSums A 2, n ≤ b ∧ b ≤ n + 1 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · exact ⟨n + 1, odd_mem_distinctSums_two he.add_one (hN (n + 1) (by omega)), by omega, le_rfl⟩
  · exact ⟨n, odd_mem_distinctSums_two ho (hN n hn), le_rfl, by omega⟩

theorem order_two_bounded_gaps (A : Set ℕ) (hA : IsAsymptoticBasis A 2) :
    HasBoundedGaps (distinctSums A 2) :=
  ⟨1, order_two_gap_le_two A hA⟩

theorem distinctSums_two_infinite (A : Set ℕ) (hA : IsAsymptoticBasis A 2) :
    (distinctSums A 2).Infinite := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  refine Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 * (N + i) + 1) ?_ ?_
  · intro i j hij
    simp only at hij
    omega
  · intro i
    exact odd_mem_distinctSums_two ⟨N + i, by ring⟩ (hN _ (by omega))

theorem exact_order_two_gap_le_two (A : Set ℕ) (hA : ∀ᶠ n in atTop, IsSumOfExactly A 2 n) :
    ∀ᶠ n in atTop, ∃ b ∈ exactDistinctSums A 2, n ≤ b ∧ b ≤ n + 1 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hA
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · exact ⟨n + 1, odd_mem_exactDistinctSums_two he.add_one (hN (n + 1) (by omega)), by omega,
      le_rfl⟩
  · exact ⟨n, odd_mem_exactDistinctSums_two ho (hN n hn), le_rfl, by omega⟩

theorem exact_order_two_bounded_gaps (A : Set ℕ) (hA : ∀ᶠ n in atTop, IsSumOfExactly A 2 n) :
    HasBoundedGaps (exactDistinctSums A 2) :=
  ⟨1, exact_order_two_gap_le_two A hA⟩

end Erdos880

#print axioms Erdos880.order_two_bounded_gaps
#print axioms Erdos880.exact_order_two_bounded_gaps
#print axioms Erdos880.isSumOfExactly_insert_zero
#print axioms Erdos880.isSumOfAtMost_of_exactly_insert_zero
